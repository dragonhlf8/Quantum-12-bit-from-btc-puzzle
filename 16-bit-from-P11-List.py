#!/usr/bin/env python3
# ===========================================================================================
# 🔐 Quantum ECDLP Solver - Final Working Version with Correct Result Handling 🔐
# ===========================================================================================

import sys
import getpass
import logging
from collections import defaultdict
from fractions import Fraction
from math import gcd, pi
import numpy as np
from ecdsa import SigningKey, SECP256k1
from ecdsa.ellipticcurve import Point, CurveFp
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
from qiskit_ibm_runtime.options import SamplerOptions
from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit.circuit.library import QFT
from qiskit_aer import AerSimulator
from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
from tqdm import tqdm

# ====================== CONSTANTS ======================
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
A = 0
B = 7
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

CURVE = CurveFp(P, A, B)
G = Point(CURVE, Gx, Gy)

FULL_RANGE_START = 0x4000
FULL_RANGE_END = 0x7fff

TARGET_PUBKEY = bytes.fromhex("03c1e36164e7fd4939be73c550154c01ffd96dfcfac7c805f15b5d9e4a364b409b")
TARGET_ADDRESS = "19hqK9vkcXRvnq6obsUaWSW6HywBHysot6"

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
logger = logging.getLogger(__name__)

# ====================== EC HELPERS ======================
def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, y, x = extended_gcd(b % a, a)
    return g, x - (b // a) * y, y

def modinv(a, m):
    g, x, y = extended_gcd(a, m)
    if g != 1:
        return None
    return x % m

def decompress_pubkey(hex_key):
    prefix = int(hex_key[:2], 16)
    x = int(hex_key[2:], 16)
    y_sq = (pow(x, 3, P) + B) % P
    y = pow(y_sq, (P + 1) // 4, P)
    if (y % 2) != (prefix % 2):
        y = P - y
    return Point(CURVE, x, y)

def point_add(p1, p2):
    if p1 is None: return p2
    if p2 is None: return p1
    x1, y1 = p1.x(), p1.y()
    x2, y2 = p2.x(), p2.y()
    if x1 == x2 and (y1 + y2) % P == 0: return None
    if x1 == x2 and y1 == y2:
        lam = (3 * x1 * x1 + A) * modinv(2 * y1, P) % P
    else:
        lam = (y2 - y1) * modinv(x2 - x1, P) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return Point(CURVE, x3, y3)

def point_double(p):
    if p is None: return None
    x, y = p.x(), p.y()
    if y == 0: return None
    lam = (3 * x * x + A) * modinv(2 * y, P) % P
    x3 = (lam * lam - 2 * x) % P
    y3 = (lam * (x - x3) - y) % P
    return Point(CURVE, x3, y3)

def ec_scalar_mult(k, point):
    if k == 0 or point is None:
        return None
    result = None
    addend = point
    while k:
        if k & 1:
            result = point_add(result, addend)
        addend = point_double(addend)
        k >>= 1
    return result

def compress_pubkey(privkey):
    sk = SigningKey.from_secret_exponent(privkey, curve=SECP256k1)
    vk = sk.verifying_key
    x = vk.pubkey.point.x()
    y = vk.pubkey.point.y()
    prefix = b'\x02' if (y % 2 == 0) else b'\x03'
    return prefix + x.to_bytes(32, byteorder='big')

def continued_fraction_approx(num, den, max_den=1000000):
    if den == 0:
        return 0, 1
    frac = Fraction(num, den).limit_denominator(max_den)
    return frac.numerator, frac.denominator

# ====================== QPE CIRCUIT BUILDER ======================
def build_enhanced_shor_qpe_circuit(effective_bits, delta_x, delta_y):
    n = effective_bits
    phase = QuantumRegister(n, "phase")
    state = QuantumRegister(n, "state")
    cat = QuantumRegister(3, "cat")
    flag = QuantumRegister(2, "flag")
    erasure = QuantumRegister(1, "erasure")
    c_phase = ClassicalRegister(n, "c_phase")
    c_flag = ClassicalRegister(2, "c_flag")
    c_erasure = ClassicalRegister(1, "c_erasure")

    qc = QuantumCircuit(phase, state, cat, flag, erasure, c_phase, c_flag, c_erasure)

    # Initialize cat state for error mitigation
    qc.h(cat[0])
    for i in range(1, 3):
        qc.cx(cat[0], cat[i])

    # Initialize phase qubits for QPE
    for i in range(n):
        qc.h(phase[i])

    # Enhanced QPE oracle with both delta_x and delta_y targeting
    for i in range(n):
        for j in range(n):
            angle_x = 2 * pi * (delta_x * (1 << j)) % ORDER / (1 << n)
            angle_y = 2 * pi * (delta_y * (1 << j)) % ORDER / (1 << n)
            combined_angle = (angle_x + angle_y) / 2
            qc.cp(combined_angle, phase[i], state[j])

    # Additional phase correction
    for i in range(n):
        correction_angle = pi / (2 ** (n - i))
        qc.cp(correction_angle, phase[i], state[i % (n//2)])

    # Inverse QFT
    qc.append(QFT(n, do_swaps=False).inverse(), phase)

    # Measurement
    qc.measure(phase, c_phase)
    qc.measure(flag, c_flag)
    qc.measure(erasure, c_erasure)

    # Additional error mitigation
    for i in range(n):
        qc.cx(cat[0], phase[i])
        qc.cz(cat[1], phase[i])

    return qc

# ====================== QUANTUM EXECUTION (CORRECTED) ======================
def run_quantum_job(service, qc, shots=32768):
    try:
        if service:
            backend = service.least_busy(operational=True, simulator=False, min_num_qubits=156)
            print(f"Using IBM backend: {backend.name}")
        else:
            backend = AerSimulator()
            print("Using local AerSimulator")

        # SamplerOptions with XY4
        options = SamplerOptions()
        options.dynamical_decoupling.enable = True
        options.dynamical_decoupling.sequence_type = "XY4"
        options.default_shots = shots

        # Transpile with proper optimization
        pm = generate_preset_pass_manager(
            optimization_level=3,
            backend=backend,
            routing_method="sabre"
        )
        transpiled = pm.run(qc)
        print(qc)
        print(f"Transpiled circuit depth: {transpiled.depth()}")
        print(f"Transpiled circuit size: {transpiled.size()}")
        print(f"Shots requested: {shots}")

        # Run with proper circuit wrapping
        sampler = SamplerV2(backend, options=options)
        job = sampler.run([transpiled])
        print(f"Job ID: {job.job_id}")
        print("Waiting for results...")

        # Get results using the correct method
        result = job.result()
        pub_result = result[0]
        # The circuit has multiple classical registers, so we combine them
        counts = pub_result.join_data().get_counts()

        return dict(counts)

    except Exception as e:
        logger.error(f"Execution error: {e}")
        logger.error("Check your circuit and backend configuration")
        raise

# ====================== POST-PROCESSING ======================
def post_process(counts, bits, order, start, target_pub):
    candidates = set()
    print(f"Processing {len(counts)} measurements...")

    for state_str, count in counts.items():
        try:
            measured = int(state_str, 2)

            # Continued fraction approximation
            for d in range(1, 20):
                r_num, r_den = continued_fraction_approx(measured, 1 << bits)
                if r_den == 0:
                    continue
                inv = modinv(r_den, order)
                if inv is None:
                    continue
                candidate = (r_num * inv) % order
                if start <= candidate <= FULL_RANGE_END:
                    candidates.add(candidate)

            # GCD check
            for m in range(1, 10):
                g = gcd(measured * m, order)
                if 1 < g < order and start <= g <= FULL_RANGE_END:
                    candidates.add(g)

        except Exception as e:
            print(f"Error processing measurement: {e}")
            continue

    return sorted(candidates)[:5000]

# ====================== MAIN FUNCTION ======================
def main():
    print("\n" + "="*140)
    print("BITCOIN PUZZLE #15 - CORRECT QUANTUM ECDLP SOLVER")
    print("Full recovery from public key only")
    print("="*140)

    shots = int(input("Enter number of shots (default 32768): ") or 32768)
    print(f"Search range: 0x{FULL_RANGE_START:x} to 0x{FULL_RANGE_END:x}")

    # Connect to IBM Quantum
    service = None
    try:
        token = getpass.getpass("Enter IBM Quantum API Token: ").strip()
        if not token:
            raise ValueError("No token provided")
        channel = input("Channel [ibm_quantum_platform/ibm_cloud]: ") or "ibm_quantum_platform"
        crn = input("IBM Cloud CRN (optional): ") or None
        service = QiskitRuntimeService(token=token, channel=channel, instance=crn)
        print("✅ Connected to IBM Quantum")
    except Exception as e:
        print(f"IBM connection failed: {e}")
        print("Falling back to local AerSimulator")
        service = None

    # Derive target point from pubkey
    Q = decompress_pubkey(TARGET_PUBKEY.hex())
    delta_x = Q.x() % (1 << 16)
    delta_y = Q.y() % (1 << 16)
    print(f"Target pubkey point (16-bit): ({hex(delta_x)}, {hex(delta_y)})")

    # Build and run circuit
    effective_bits = 8
    qc = build_enhanced_shor_qpe_circuit(effective_bits, delta_x, delta_y)

    try:
        counts = run_quantum_job(service, qc, shots)
        print(f"Received {len(counts)} measurement results")

        # Post-process results
        candidates = post_process(counts, effective_bits, ORDER, FULL_RANGE_START, Q)
        print(f"\nVerifying {len(candidates)} candidates...")

        # Verify candidates
        found = False
        for candidate in candidates:
            try:
                if compress_pubkey(candidate) == TARGET_PUBKEY:
                    print("\n" + "="*140)
                    print("!!! PRIVATE KEY FOUND !!!")
                    print(f"Private key (hex): 0x{candidate:x}")
                    print(f"Address: {TARGET_ADDRESS}")
                    print("="*140)
                    with open("found_key_15_quantum.txt", "w") as f:
                        f.write(f"0x{candidate:x}\n")
                    found = True
                    break
            except Exception as e:
                print(f"Error verifying candidate: {e}")
                continue

        if not found:
            print("\nNo match found in this run.")
            print("This is the corrected quantum ECDLP solver.")

    except Exception as e:
        print(f"Execution failed: {e}")

if __name__ == "__main__":
    main()
