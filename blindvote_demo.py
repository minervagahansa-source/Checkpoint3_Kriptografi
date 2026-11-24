import hashlib
import math
import secrets
import sys
import time

# --------------------------------------------------------------------------
# 1. Fondasi matematika (Minggu 3)
# --------------------------------------------------------------------------
# Daftar bilangan prima kecil dipakai sebagai saringan awal (trial division)
# sebelum menjalankan uji Miller-Rabin agar kandidat komposit kecil cepat gugur.

_SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def is_probable_prime(n: int, rounds: int = 40) -> bool:
    """
    Uji Primalitas Probabilistik Miller-Rabin:
    - Menulis n - 1 = d * 2^s dengan d bilangan ganjil.
    - Untuk tiap saksi acak 'a' pada [2, n - 2], hitung x = a^d mod n.
    - Jika n prima, x == 1 atau x == n - 1 (mod n), atau pemangkatan berulang
      x <- x^2 mod n akan mencapai n - 1 sebelum mencapai 1.
    - Jika gagal pada salah satu putaran, n dipastikan komposit (False).
    - Dengan 40 putaran acak, peluang komposit lolos (kesalahan false positive)
      paling besar (1/4)^40 = 2^-80 (sangat kecil untuk praktik kriptografi).
    """
    if n < 2:
        return False
    for sp in _SMALL_PRIMES:
        if n % sp == 0:
            return n == sp

    # Dekomposisi n - 1 menjadi d * 2^s (d ganjil, s >= 0)
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1

    # Pengujian probabilistik sebanyak 'rounds' putaran
    for _ in range(rounds):
        a = secrets.randbelow(n - 3) + 2    # pilih saksi acak a di [2, n - 2]
        x = pow(a, d, n)                    # modular exponentiation: a^d mod n
        if x in (1, n - 1):
            continue

        # Kuadratkan berulang hingga s - 1 kali untuk mencari akar kuadrat nontrivial dari 1
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:

            # Tidak pernah menjadi n - 1 -> pasti komposit
            return False
    return True


def gen_prime(bits: int) -> int:

    """
    Membangkitkan bilangan prima acak berukuran 'bits' bit secara kriptografis:
    - secrets.randbits(bits) menghasilkan bit acak aman (CSPRNG).
    - (1 << (bits - 1)) memaksa MSB = 1 agar panjang bit tepat 'bits'.
    - | 1 memaksa LSB = 1 agar kandidat selalu ganjil (bilangan prima > 2 ganjil).
    - Diuji dengan Miller-Rabin sampai lolos.
    """

    while True:
        cand = secrets.randbits(bits) | (1 << (bits - 1)) | 1
        if is_probable_prime(cand):
            return cand


def egcd(a: int, b: int):

    """
    Algoritma Extended Euclidean (Extended Euclid):
    - Mencari tupel (g, x, y) sehingga memenuhi Persamaan Bezout:
        a * x + b * y = g, dengan g = gcd(a, b).
    - Menggunakan pembagian berulang (Euclidean algorithm) sambil memperbarui
      koefisien kombinasi linear (x0, x1) dan (y0, y1) pada tiap langkah.
    """

    x0, y0, x1, y1 = 1, 0, 0, 1
    while b:
        q = a // b
        a, b = b, a - q * b
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return a, x0, y0


def modinv(a: int, m: int) -> int:

    """
    Invers Modulo (Modular Multiplicative Inverse):
    - Mencari nilai x sehingga (a * x) mod m = 1, dinotasikan a^-1 mod m.
    - Invers modulo hanya ada jika gcd(a, m) == 1 (a dan m saling prima / koprima).
    - Jika g != 1, lempar ValueError karena invers tidak terdefinisi.
    - Normalisasi hasil dengan x % m agar berada pada rentang [0, m - 1].
    """
    
    g, x, _ = egcd(a % m, m)
    if g != 1:
        raise ValueError("invers modulo tidak ada (gcd != 1)")
    return x % m


def keygen(bits: int = 2048, e: int = 65537):

    """
    Pembangkitan Pasangan Kunci RSA (Key Generation):
    1. Pilih dua prima acak p dan q masing-masing berukuran bits // 2 (1024-bit untuk RSA-2048).
    2. Hitung lam = lcm(p - 1, q - 1) (Carmichael function lambda(n); versi ringkas dari totient).
    3. Pastikan gcd(e, lam) == 1 agar eksponen publik e memiliki invers modulo.
    4. Hitung modulus publik n = p * q (panjang tepat 'bits' bit).
    5. Hitung kunci privat (trapdoor) d = e^-1 mod lam menggunakan Extended Euclid / modinv.
       Tanpa mengetahui faktorisasi p dan q dari n, menghitung d secara langsung sangat sulit.
    """

    while True:
        p, q = gen_prime(bits // 2), gen_prime(bits // 2)
        if p == q:
            continue
        lam = math.lcm(p - 1, q - 1)
        if math.gcd(e, lam) != 1:
            continue
        n = p * q
        if n.bit_length() != bits:
            continue
        d = modinv(e, lam)
        return (n, e), (n, d)


def fdh(data: bytes, n: int) -> int:

    """
    Full-Domain Hash (FDH) berbasis SHA-256:
    - Mengubah pesan byte berukuran sembarang menjadi bilangan bulat dalam rentang [0, n - 1].
    - Karena SHA-256 hanya menghasilkan digest 256-bit (32 byte), sedangkan modulus n
      berukuran 2048-bit (256 byte), digest diperluas menggunakan counter 4-byte
      (ctr || data) hingga panjang byte mencukupi (k = panjang byte n + 16 byte margin),
      lalu direduksi modulo n.
    - Mencegah serangan multiplikatif pada RSA mentah (unhashed RSA).
    """

    k = (n.bit_length() + 7) // 8 + 16
    out, ctr = b"", 0
    while len(out) < k:
        out += hashlib.sha256(ctr.to_bytes(4, "big") + data).digest()
        ctr += 1
    return int.from_bytes(out[:k], "big") % n





# --------------------------------------------------------------------------
# 2. Aktor protokol
# --------------------------------------------------------------------------
# Identitas pemilihan mencegah penggunaan ulang tanda tangan/surat suara
# lintas pemilu atau konteks yang berbeda (domain separation).

ELECTION_ID = b"BEM-FMIPA-2026/v1"


def ballot_message(t: bytes, vote: str) -> bytes:

    """
    Encoding kanonik dengan awalan panjang (length-prefixed encoding):
    - Setiap bagian (ELECTION_ID, token t, pilihan vote) diawali panjangnya dalam
      2 byte big-endian agar gabungan byte tidak ambigu / tidak bisa salah parsed.
    """

    parts = [ELECTION_ID, t, vote.encode()]
    return b"".join(len(p).to_bytes(2, "big") + p for p in parts)


class Registrar:

    """
    Panitia (Registrar):
    - Memegang pasangan kunci RSA; kunci privat d bersifat rahasia (trapdoor).
    - Memverifikasi hak pilih (eligibility) dan memastikan satu pemilih hanya
      menerima satu tanda tangan buta (uniqueness saat penerbitan).
    - Menandatangani nilai tersamar m' tanpa pernah melihat isi suara v maupun token t.
    """

    def __init__(self, bits=2048):
        self.pub, self._priv = keygen(bits)
        self.issued = set()                             # voter_id yang sudah menerima tanda tangan

    def sign_blinded(self, voter_id: str, eligible: bool, blinded: int) -> int:
        if not eligible:
            raise PermissionError("bukan pemilih terdaftar")
        if voter_id in self.issued:
            raise PermissionError("token sudah pernah diterbitkan")
        n, d = self._priv

        # Validasi dasar nilai tersamar m' agar berada dalam rentang valid dan koprima dengan n
        if not (1 < blinded < n) or math.gcd(blinded, n) != 1:
            raise ValueError("nilai tersamar tidak valid")
        self.issued.add(voter_id)

        # Penandatanganan buta: s' = (m')^d mod n
        return pow(blinded, d, n)


class BallotBox:

    """
    Kotak suara (BallotBox):
    - Hanya memegang kunci publik (n, e) milik panitia.
    - Menerima (t, vote, s) lewat kanal terpisah dari proses autentikasi/penerbitan.
    - Menolak token yang sudah terpakai (mencegah replay / double voting) dan
      memverifikasi tanda tangan s^e mod n == fdh(ballot_message(t, vote), n).
    """

    def __init__(self, registrar_pub):
        self.n, self.e = registrar_pub
        self.used = set()
        self.bulletin = []                   # papan pengumuman publik

    def cast(self, t: bytes, vote: str, s: int) -> bool:
        if t in self.used:
            return False                     # replay / double voting
        m = fdh(ballot_message(t, vote), self.n)

        # Verifikasi tanda tangan RSA: jika sah, s^e mod n == m^d^e mod n == m
        if pow(s, self.e, self.n) != m:
            return False                     # tanda tangan tidak sah / suara dimodifikasi
        self.used.add(t)
        self.bulletin.append((t.hex()[:16], vote))
        return True


class Voter:
    
    """
    Pemilih (Voter / Alice):
    1. Membuat token acak 256-bit 't' dan menghitung hash surat suara m = fdh(..., n).
    2. Memilih faktor penyamar (blinding factor) 'r' acak dengan gcd(r, n) == 1.
    3. Menyamar m menjadi m' = m * r^e mod n sebelum dikirim ke Panitia.
    4. Melepas penyamaran dari tanda tangan panitia s' menggunakan invers r^-1 mod n:
         s = s' * r^-1 mod n = (m * r^e)^d * r^-1 = m^d * r^(e*d - 1) = m^d mod n
       karena e * d ≡ 1 (mod lcm(p-1, q-1)).
    """

    def __init__(self, registrar_pub, vote: str):
        self.n, self.e = registrar_pub
        self.vote = vote
        self.t = secrets.token_bytes(32)    # serial token acak 256-bit
        self.m = fdh(ballot_message(self.t, vote), self.n)
        while True:                         # r harus punya invers mod n  <=>  gcd(r, n) = 1
            self.r = secrets.randbelow(self.n - 2) + 2
            if math.gcd(self.r, self.n) == 1:
                break

    def blind(self) -> int:

        # m' = m * r^e mod n: menyamarkan m sehingga Panitia tidak tahu isinya
        return (self.m * pow(self.r, self.e, self.n)) % self.n

    def unblind(self, s_blind: int) -> int:

        # s = s' * r^-1 mod n: mengembalikan tanda tangan atas pesan asli m
        s = (s_blind * modinv(self.r, self.n)) % self.n

        # Verifikasi lokal untuk mendeteksi jika m' atau s' diubah saat transmisi
        if pow(s, self.e, self.n) != self.m:
            raise ValueError("tanda tangan tidak valid (ada yang mengubah!)")
        return s





# --------------------------------------------------------------------------
# 3. Tampilan (hanya pemformatan keluaran, tidak mengubah logika kripto)
# --------------------------------------------------------------------------

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")  # agar simbol tampil di Windows

_USE_COLOR = sys.stdout.isatty()


def _c(text, code):
    return f"\033[{code}m{text}\033[0m" if _USE_COLOR else text


GREEN = lambda s: _c(s, "32;1")
RED = lambda s: _c(s, "31;1")
BLUE = lambda s: _c(s, "34;1")
DIM = lambda s: _c(s, "2")
BOLD = lambda s: _c(s, "1")
WIDTH = 74
RESULTS = []                                  # (kode, skenario, ekspektasi, lulus)


def short(x: int, keep: int = 10) -> str:

    """Tampilkan bilangan besar secara ringkas: 0x1a2b...9f0e (2048 bit)."""

    h = f"{x:x}"
    return f"0x{h}" if len(h) <= 2 * keep + 3 else f"0x{h[:keep]}…{h[-keep:]} ({x.bit_length()} bit)"


def banner():
    print("╔" + "═" * (WIDTH - 2) + "╗")
    for line in ("BlindVote  ·  Demo E-Voting RSA Blind Signature",
                 "Checkpoint 3 · Kriptografi · Matematika Minggu 3"):
        print("║" + BOLD(line.center(WIDTH - 2)) + "║")
    print("╚" + "═" * (WIDTH - 2) + "╝")


def section(title):
    print("\n" + BLUE("▌ " + title))
    print(DIM("─" * WIDTH))


def info(label, value):
    print(f"   {label:<26}{value}")


def check(kode, skenario, ekspektasi, lulus, detail=""):
    RESULTS.append((kode, skenario, ekspektasi, lulus))
    tag = GREEN("[ LULUS ]") if lulus else RED("[ GAGAL ]")
    print(f"   {tag} {BOLD(kode)}  {skenario}")
    print(f"             {DIM('harapan:')} {ekspektasi}")
    if detail:
        print(f"             {DIM('detail :')} {detail}")


def summary():
    section("RINGKASAN HASIL")
    w = [4, 48]
    top = "┌" + "─" * (w[0] + 2) + "┬" + "─" * (w[1] + 2) + "┬────────┐"
    mid = "├" + "─" * (w[0] + 2) + "┼" + "─" * (w[1] + 2) + "┼────────┤"
    bot = "└" + "─" * (w[0] + 2) + "┴" + "─" * (w[1] + 2) + "┴────────┘"
    print(top)
    print(f"│ {'Kode':<{w[0]}} │ {'Skenario':<{w[1]}} │ Status │")
    print(mid)
    for kode, sk, ek, ok in RESULTS:
        st = GREEN("LULUS ") if ok else RED("GAGAL ")
        print(f"│ {kode:<{w[0]}} │ {sk[:w[1]]:<{w[1]}} │ {st} │")
    print(bot)
    total, ok = len(RESULTS), sum(1 for r in RESULTS if r[3])
    msg = f"{ok}/{total} skenario sesuai desain"
    print("\n   " + (GREEN("✔ " + msg) if ok == total else RED("✘ " + msg)))





# --------------------------------------------------------------------------
# 4. Skenario uji
# --------------------------------------------------------------------------
def demo_toy():

    """T0: Simulasi perhitungan tangan dengan bilangan kecil (p=61, q=53, e=17)."""

    section("T0 · Contoh mini dengan angka kecil (bisa dihitung tangan)")
    p, q, e = 61, 53, 17
    n = p * q
    d = modinv(e, math.lcm(p - 1, q - 1))
    m, r = 65, 7
    blinded = (m * pow(r, e, n)) % n
    s_blind = pow(blinded, d, n)
    s = (s_blind * modinv(r, n)) % n
    info("Kunci", f"p={p}, q={q}, n={n}, e={e}")
    info("Trapdoor d", f"{d}   (e·d mod λ(n) = {(e * d) % math.lcm(p - 1, q - 1)})")
    info("Surat suara m, faktor r", f"m={m}, r={r}, r⁻¹={modinv(r, n)}")
    info("Dilihat panitia m′", f"{blinded}")
    info("Tanda tangan buta s′", f"{s_blind}")
    info("Setelah dilepas s", f"{s}   (pembanding m^d mod n = {pow(m, d, n)})")
    check("T0", "Penyamaran dapat dilepas: s = m^d mod n",
          "s sama dengan m^d mod n", s == pow(m, d, n))


def main():
    t0 = time.time()
    banner()
    demo_toy()

    section("PERSIAPAN · Membuat kunci RSA-2048 (Miller-Rabin)")
    print("   Mencari dua bilangan prima 1024-bit, mohon tunggu beberapa detik...")
    reg = Registrar(2048)
    box = BallotBox(reg.pub)
    n, e = reg.pub
    _, d = reg._priv
    info("n  (publik)", short(n))
    info("e  (publik)", str(e))
    info("d  (trapdoor, rahasia)", "disimpan hanya oleh panitia")
    info("Waktu pembuatan kunci", f"{time.time() - t0:.1f} detik")

    section("SKENARIO PROTOKOL")

    # T1: Alur normal pemungutan suara dari penyamaran hingga masuk papan pengumuman
    alice = Voter(reg.pub, "Calon-02")
    s = alice.unblind(reg.sign_blinded("2300001", True, alice.blind()))
    ok = box.cast(alice.t, alice.vote, s)
    check("T1", "Pemungutan suara normal", "suara diterima Kotak Suara", ok,
          f"token t = {alice.t.hex()[:16]}…")

    # T2: Pemilih yang sama mencoba meminta tanda tangan / token kedua kalinya
    try:
        reg.sign_blinded("2300001", True, Voter(reg.pub, "Calon-01").blind())
        ok, det = False, "panitia menerbitkan token kedua"
    except PermissionError as ex:
        ok, det = True, f"panitia menolak: {ex}"
    check("T2", "Pemilih meminta token dua kali", "ditolak panitia", ok, det)

    # T3: Eve mengubah pilihan (vote) di jaringan setelah tanda tangan diterbitkan
    ok = not box.cast(alice.t, "Calon-01", s)
    check("T3", "Eve mengganti isi suara di jaringan", "ditolak (tanda tangan tak cocok)", ok)

    # T4: Eve mengirim ulang (replay) paket suara yang sudah sah dan tercatat
    ok = not box.cast(alice.t, alice.vote, s)
    check("T4", "Eve mengirim ulang suara sah (replay)", "ditolak (token terpakai)", ok)

    # T5: Eve memodifikasi nilai tersamar m' yang dikirim ke panitia
    bob = Voter(reg.pub, "Calon-01")
    s_bad = reg.sign_blinded("2300002", True, (bob.blind() * 2) % n)
    try:
        bob.unblind(s_bad)
        ok, det = False, "manipulasi tidak terdeteksi"
    except ValueError as ex:
        ok, det = True, f"Alice mendeteksi: {ex}"
    check("T5", "Eve mengubah nilai tersamar ke panitia", "terdeteksi saat pelepasan", ok, det)

    # T6: Seseorang mengirim tanda tangan acak tanpa kunci privat d
    ok = not box.cast(secrets.token_bytes(32), "Calon-01", secrets.randbelow(n))
    check("T6", "Tanda tangan palsu acak", "ditolak", ok)

    # T7: Uji unlinkability — untuk satu nilai m' yang sama, pemegang d dapat
    # membentuk r yang cocok untuk kandidat manapun sehingga m' tidak membocorkan pilihan
    blinded_seen = Voter(reg.pub, "Calon-01").blind()  # yang dilihat panitia
    cocok = []
    for label in ("Calon-01", "Calon-02", "Calon-03"):
        m_x = fdh(ballot_message(b"token-sembarang-" + label.encode(), label), n)
        r_x = pow((blinded_seen * modinv(m_x, n)) % n, d, n)
        cocok.append((m_x * pow(r_x, e, n)) % n == blinded_seen)
    check("T7", "Apakah m′ membocorkan pilihan?", "setiap kandidat punya r yang cocok",
          all(cocok), "ada r untuk Calon-01, Calon-02, Calon-03 → tidak ada informasi bocor")

    # T8: Uji sifat multiplikatif RSA mentah (bisa dirakit) vs FDH (menolak rakitan)
    m1, m2 = 12345, 67890
    mentah = (pow(m1, d, n) * pow(m2, d, n)) % n == pow((m1 * m2) % n, d, n)
    h1, h2 = fdh(b"a", n), fdh(b"b", n)
    fdh_aman = pow((pow(h1, d, n) * pow(h2, d, n)) % n, e, n) != fdh(b"ab", n)
    check("T8", "RSA mentah vs Full-Domain Hash", "mentah bisa dirakit, FDH tidak",
          mentah and fdh_aman,
          f"mentah dapat dirakit: {mentah}; FDH menolak rakitan: {fdh_aman}")

    section("PAPAN PENGUMUMAN PUBLIK")
    for i, (tok, vote) in enumerate(box.bulletin, 1):
        print(f"   {i}. token {tok}…  →  {vote}")
    print(DIM(f"   total suara sah tercatat: {len(box.bulletin)}"))

    summary()
    print(DIM(f"\n   Selesai dalam {time.time() - t0:.1f} detik.\n"))
    sys.exit(0 if all(r[3] for r in RESULTS) else 1)


if __name__ == "__main__":
    main()