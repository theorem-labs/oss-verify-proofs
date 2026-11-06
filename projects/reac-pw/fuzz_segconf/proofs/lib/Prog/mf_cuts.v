(** m_file (plain build, image 3776ca44d75c, 0x13fb4): the cuts inside one line of the piece S_MF_LINE of
    Prog/m_file_c.v (family F3). Statement text, plus the proof that the sub-pieces give
    S_MF_LINE (mf_line_from_parts: logic only).

    S_MF_LINE is `forall n, H_MF_TAIL n -> H_MF_HEAD (S n)`: one line, 0x1407c-0x143d4 and 0x143e0-0x14748. It is
    cut here at the dispatch points of the line:
    - LONG 0x140bc: the line has 512 bytes or more (`bge s8` 0x140b8 not taken).
    - HDR 0x14188 / KEY 0x14200: the line is short, comment-cut and stripped to sl = [s, e) (s5, s6), sl nonempty;
      its first byte is '[' (HDR, m_header inline) or not (KEY, m_key inline). a2 = e - s (0x1417c).
    - HFIND 0x14488 (inside m_header): the header passed its checks (']' last, "segment" and a blank, a name of
      1 .. 15 bytes); s5 = the name, s6 = its length; `jal m_find` follows.
    - KDISP 0x142f8 (inside m_key): cur is Some gi, the '=' was found, the key k = [s5, s5 + s8) and the value
      v = [s4, s4 + s7) are stripped (and v unquoted); the ieq chain "role" (0x14308), "model" (0x144e4),
      "ignore" (0x145b0), "knock" (0x145ec) follows. KMODEL 0x144d4, KIGN 0x145a0, KKNOCK 0x145dc are the same
      state after the earlier words missed.
    Every cut's post is the function's post (mf_post: seg_env.ret_void_fp with the saved ra0, sp0, e0 .. e11 and
    M_FILE_W of the final model) from the final model mf_fin st line rest = fst (m_lines st (line + 1) (lines
    rest')), st the line's step and rest' the text after the line. Inside a line, s2 already holds the next line's
    address mf_next p rest and s3 = line + 1. The tail is H_MF_TAIL (pred of the head's bound): each sub-piece
    takes it as a premise and reaches it with (st, line + 1, rest').

    The sub-pieces (each `forall n, H_MF_TAIL n -> <its exit cuts> -> <its entry cut>`), files, callees:
    - S_MF_FRONT (Prog/mf_line_front.v): HEAD -> LONG, HDR, KEY or TAIL (empty stripped line). strchr 0x14088,
      strlen 0x1409c; the comment scan 0x140e0-0x14118; the strip 0x1411c-0x14170.
    - S_MF_LONGP (Prog/mf_line_front.v): LONG -> TAIL. The blank skip 0x140bc-0x140dc, cur = NULL on '['
      (0x143b0-0x143c4), m_refuse 0x143d0.
    - S_MF_HDRA (Prog/mf_line_hdra.v): HDR -> HFIND or TAIL (the refusals 0x144c8, 0x14644). memchr 0x14190,
      the strips 0x141a4-0x141fc and 0x14414-0x14474, ieq "segment" 0x14400.
    - S_MF_HDRB (Prog/mf_line_hdrb.v): HFIND -> TAIL. m_find 0x14494; found: gen test 0x144ac, m_refuse 0x144b8,
      g->gen = c->gen 0x14720; new: n < 32 (0x1462c), n++ 0x146e8, memset 0x146fc, memcpy 0x14710, gen; full:
      overflow++ 0x14638 and m_refuse 0x14644.
    - S_MF_KEYA (Prog/mf_line_keya.v): KEY -> KDISP or TAIL (cur NULL or no '=': m_refuse 0x143d0). memchr
      0x14208, the strips 0x14218-0x142b4, the quotes 0x142b8-0x142ec.
    - S_MF_KROLE (Prog/mf_line_krole.v): KDISP -> KMODEL or TAIL. ieq "role" 0x14308, the fold 0x14310-0x1435c,
      the words loop 0x1436c-0x1439c (strlen 0x14374, bcmp 0x14388), the stores 0x14568-0x14578, snprintf
      0x14590, m_refuse 0x143a8.
    - S_MF_KMOD (Prog/mf_line_kmodel.v): KMODEL -> KIGN or TAIL. ieq "model" 0x144e4, the fold 0x144ec-0x14534,
      fuzz_catalogue_row 0x14540, memcpy 0x14558, model_set 0x14560, m_refuse 0x14744.
    - S_MF_KIGNP (Prog/mf_line_kign.v): KIGN -> KKNOCK or TAIL. ieq "ignore" 0x145b0, ieq "yes" / "true" / "no" /
      "false" (0x145c8, 0x14660, 0x14690, 0x146a8), "1" / "0", the stores 0x146b8 / 0x146c0, snprintf 0x146d8,
      m_refuse 0x14744.
    - S_MF_KKNOCKP (Prog/mf_line_kign.v): KKNOCK -> TAIL. ieq "knock" 0x145ec, kept_knock[n_kept] = 1 0x1461c,
      m_refuse 0x143d0 (knock = true) or 0x143a8 (an unknown key). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c mfu_facts.
Import ListNotations.
Open Scope Z_scope.

Definition MF_PC_LONG : Z := 0x140bc.
Definition MF_PC_HDR : Z := 0x14188.
Definition MF_PC_KEY : Z := 0x14200.
Definition MF_PC_HFIND : Z := 0x14488.
Definition MF_PC_KDISP : Z := 0x142f8.
Definition MF_PC_KMODEL : Z := 0x144d4.
Definition MF_PC_KIGN : Z := 0x145a0.
Definition MF_PC_KKNOCK : Z := 0x145dc.

(** ** The post
    The line terms (mf_line, mf_rest, mf_next), the final model mf_fin and the two partial steps mh_find (m_header
    after its name checks) and mk_disp (m_key after the key and value are cut) are build-independent and shared with
    the UBSan twin: Prog/mfu_facts.v. *)
(** The function's post from a cut: return to ra0 with sp0 and the entry s0 .. s11, the writes in M_FILE_W of the
    final model mf, and the block holding mf. *)
Definition mf_post (ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (F : bvmap 5 word)
    (m : word -> option byte) (lo c : Z) (k0 : nat) (mf : mconf) : machine_state -> Prop :=
  ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m (M_FILE_W (bv_unsigned sp0) c k0 mf) lo
    (fun m' => mconf_at rsegs m' c mf).

(** ** The cuts
    Common premises: the line-loop facts of the head (m_file_loop, with the head's line number [line] and text
    [rest]: nothing the line writes has happened yet, the callees before a cut write only below sp), rest <> [],
    the bound (length rest <= n) and the loop registers with s2 = mf_next p rest and s3 = line + 1. *)

Definition H_MF_LONG (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c (mf_next p rest) (line + 1) s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
    s5 = Z_to_bv 64 p -> s6 = Z_to_bv 64 (p + Z.of_nat (length (mf_line rest))) ->
    (512 <= length (mf_line rest))%nat ->
    evt rsegs
      (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (m_line (mc, cur) (line + 1) (mf_line rest)) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MF_PC_LONG) fc None m (seg_rom rsegs)).

(** HDR: sl = h_strip (h_cut_comment l) = the bytes [i, j) of the line l, its first byte '['. *)
Definition H_MF_HDR (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z) (i j : nat),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c (mf_next p rest) (line + 1) s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
    (length (mf_line rest) < 512)%nat ->
    (i < j)%nat -> (j <= length (mf_line rest))%nat ->
    slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)) ->
    nth i (mf_line rest) 0 = LBR ->
    s5 = Z_to_bv 64 (p + Z.of_nat i) -> s6 = Z_to_bv 64 (p + Z.of_nat j) -> a2 = Z_to_bv 64 (Z.of_nat (j - i)) ->
    evt rsegs
      (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (m_header mc (h_strip (h_cut_comment (mf_line rest))) (line + 1)) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MF_PC_HDR) fc None m (seg_rom rsegs)).

(** KEY: as HDR, the first byte not '['. *)
Definition H_MF_KEY (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z) (i j : nat),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c (mf_next p rest) (line + 1) s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
    (length (mf_line rest) < 512)%nat ->
    (i < j)%nat -> (j <= length (mf_line rest))%nat ->
    slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)) ->
    nth i (mf_line rest) 0 <> LBR ->
    s5 = Z_to_bv 64 (p + Z.of_nat i) -> s6 = Z_to_bv 64 (p + Z.of_nat j) -> a2 = Z_to_bv 64 (Z.of_nat (j - i)) ->
    evt rsegs
      (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (m_key mc cur (h_strip (h_cut_comment (mf_line rest))) (line + 1), cur) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MF_PC_KEY) fc None m (seg_rom rsegs)).

(** HFIND: the name nm = the bytes [o, o + |nm|) of the text left (inside the line), 1 <= |nm| <= 15, in s5 / s6
    (s6 = the length); s7 = 9 again (0x14448), so the loop registers hold. The step is mh_find. *)
Definition H_MF_HFIND (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z) (o : nat) (nm : list Z),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    m_file_regs c (mf_next p rest) (line + 1) s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
    (0 < length nm < 16)%nat -> (o + length nm <= length (mf_line rest))%nat ->
    firstn (length nm) (skipn o rest) = nm ->
    s5 = Z_to_bv 64 (p + Z.of_nat o) -> s6 = Z_to_bv 64 (Z.of_nat (length nm)) ->
    evt rsegs
      (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (mh_find mc nm (line + 1)) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MF_PC_HFIND) fc None m (seg_rom rsegs)).

(** The key state shared by KDISP, KMODEL, KIGN and KKNOCK: cur = Some gi; the key k = the bytes [ok, ok + kl) and
    the value v = the bytes [ov, ov + vl) of the text left, both inside the line; s5 = k, s8 = kl, s4 = v, s7 = vl,
    s6 = the value's end (m_key borrows s7 and s8: every path puts 9 and 0x1ff back before the tail). *)
Definition mk_regs (c p line : Z) (rest : list Z) (ok kl ov vl : nat)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  s0 = Z_to_bv 64 c /\ s1 = Z_to_bv 64 0x3b /\ s2 = Z_to_bv 64 (mf_next p rest) /\ s3 = Z_to_bv 64 (line + 1) /\
  s9 = Z_to_bv 64 BLANK_MASK /\ s10 = Z_to_bv 64 0x23 /\ s11 = Z_to_bv 64 0x20 /\
  s5 = Z_to_bv 64 (p + Z.of_nat ok) /\ s8 = Z_to_bv 64 (Z.of_nat kl) /\
  s4 = Z_to_bv 64 (p + Z.of_nat ov) /\ s7 = Z_to_bv 64 (Z.of_nat vl) /\
  s6 = Z_to_bv 64 (p + Z.of_nat (ov + vl)).
Definition mk_kv (rest : list Z) (ok kl ov vl : nat) (k v : list Z) : Prop :=
  (ok + kl <= length (mf_line rest))%nat /\ (ov + vl <= length (mf_line rest))%nat /\
  firstn kl (skipn ok rest) = k /\ firstn vl (skipn ov rest) = v.

(** KDISP (pc), with the words already missed [missed] (KDISP [], KMODEL [S_role], KIGN [S_role; S_model],
    KKNOCK [S_role; S_model; S_ignore]). The step is mk_disp. *)
Definition H_MF_KAT (pc : Z) (missed : list (list Z)) (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (gi : nat) (k0 : nat) (rest : list Z) (ok kl ov vl : nat) (k v : list Z),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc (Some gi) line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    mk_regs c p line rest ok kl ov vl s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
    mk_kv rest ok kl ov vl k v ->
    Forall (fun w => ieq k w = false) missed ->
    evt rsegs
      (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Definition H_MF_KDISP (n : nat) : Prop := H_MF_KAT MF_PC_KDISP [] n.
Definition H_MF_KMODEL (n : nat) : Prop := H_MF_KAT MF_PC_KMODEL [S_role] n.
Definition H_MF_KIGN (n : nat) : Prop := H_MF_KAT MF_PC_KIGN [S_role; S_model] n.
Definition H_MF_KKNOCK (n : nat) : Prop := H_MF_KAT MF_PC_KKNOCK [S_role; S_model; S_ignore] n.

(** ** The sub-pieces of S_MF_LINE *)
Definition S_MF_FRONT : Prop :=
  forall n, H_MF_TAIL n -> H_MF_LONG n -> H_MF_HDR n -> H_MF_KEY n -> H_MF_HEAD (S n).
Definition S_MF_LONGP : Prop := forall n, H_MF_TAIL n -> H_MF_LONG n.
Definition S_MF_HDRA : Prop := forall n, H_MF_TAIL n -> H_MF_HFIND n -> H_MF_HDR n.
Definition S_MF_HDRB : Prop := forall n, H_MF_TAIL n -> H_MF_HFIND n.
Definition S_MF_KEYA : Prop := forall n, H_MF_TAIL n -> H_MF_KDISP n -> H_MF_KEY n.
Definition S_MF_KROLE : Prop := forall n, H_MF_TAIL n -> H_MF_KMODEL n -> H_MF_KDISP n.
Definition S_MF_KMOD : Prop := forall n, H_MF_TAIL n -> H_MF_KIGN n -> H_MF_KMODEL n.
Definition S_MF_KIGNP : Prop := forall n, H_MF_TAIL n -> H_MF_KKNOCK n -> H_MF_KIGN n.
Definition S_MF_KKNOCKP : Prop := forall n, H_MF_TAIL n -> H_MF_KKNOCK n.

Lemma mf_line_from_parts :
  S_MF_FRONT -> S_MF_LONGP -> S_MF_HDRA -> S_MF_HDRB -> S_MF_KEYA -> S_MF_KROLE -> S_MF_KMOD -> S_MF_KIGNP ->
  S_MF_KKNOCKP -> S_MF_LINE.
Proof.
  intros FR LG HA HB KA KR KM KI KK n HT.
  pose proof (KK n HT) as HKK. pose proof (KI n HT HKK) as HKI. pose proof (KM n HT HKI) as HKM.
  pose proof (KR n HT HKM) as HKD. pose proof (KA n HT HKD) as HKY.
  pose proof (HB n HT) as HHF. pose proof (HA n HT HHF) as HHD.
  exact (FR n HT (LG n HT) HHD HKY).
Qed.
