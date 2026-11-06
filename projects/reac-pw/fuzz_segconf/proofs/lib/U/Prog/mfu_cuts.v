(** m_file (UBSan build, image 1696d6c34ffd, 0x14268): the cuts inside one line of the piece S_MF_LINE of
    U/Prog/m_file_c.v (family F3). Statement text, plus the proof that the sub-pieces give S_MF_LINE
    (mfu_line_from_parts: logic only). The split is the plain build's (Prog/mf_cuts.v), at this build's addresses;
    the model terms (mf_line, mf_rest, mf_next, mf_fin, mh_find, mk_disp) are the shared ones of Prog/mfu_facts.v.

    S_MF_LINE is `forall n, H_MF_TAIL n -> H_MF_HEAD (S n)`: one line, 0x14348-0x146b4 and 0x146c0-0x1497c. Cut points:
    - LONG 0x143a4: the line has 512 bytes or more (`bge s6` 0x143a0 not taken); s5 = p, a0 = the line's end.
    - HDR 0x14434 / KEY 0x14528: the line is short, comment-cut (0x143c8-0x14404) and stripped by `jal strip`
      (0x14410, cells 0x40(sp) / 0x38(sp)) to sl = [s, e) (s5, s4), sl nonempty; its first byte is '[' (HDR, m_header
      inline) or not (KEY, m_key inline); a2 = e - s (0x14428).
    - HFIND 0x144ec (inside m_header): the header passed its checks (memchr ']' last, strip, ieq "segment", the blank,
      strip, a name of 1 .. 15 bytes); a1 = the name (also in the cell 0x98(sp), which 0x14930 reloads for memcpy),
      s5 = its length; `jal m_find` 0x144f4 follows.
    - KDISP 0x145d8 (inside m_key): cur is Some gi, the '=' was found, the key k (cell 0xa0(sp), a0) of kl bytes (s6)
      and the value v (cell 0x90(sp)) of vl bytes (s5) are stripped (two `jal strip`, 0x14564 / 0x14570) and v is
      unquoted; the ieq chain "role" (0x145e4), "model" (0x146d0), "ignore" (0x1478c), "knock" (0x147dc) follows.
      KMODEL 0x146c0, KIGN 0x1477c, KKNOCK 0x147cc are the same state after the earlier words missed (each reloads
      k from 0xa0(sp)).
    Every cut's post is the function's post (mfu_post: seg_env.ret_void_fp with the saved ra0, sp0, e0 .. e11 and
    M_FILE_W of the final model) from the final model mf_fin st line rest, st the line's step. Inside a line s2
    already holds the next line's address mf_next p rest and s3 = line + 1; s6 = 511 except in m_key after KDISP
    (s6 = kl there; every path puts 0x1ff back before the tail), s4 is 1 at the head and the tail and free in between.
    Every cut states the loop facts of the head (m_file_loop with the head's line number and text) of the memory at
    the cut: nothing before a cut writes the block, and the callees before it write only the stack below sp and the
    scratch cells of the frame (0x30 .. 0xa8), which m_file_loop does not fix except cur at 0x30. The tail is
    H_MF_TAIL: each sub-piece takes it as a premise and reaches it with (st, line + 1, mf_rest rest).

    The sub-pieces (each `forall n, H_MF_TAIL n -> <its exit cuts> -> <its entry cut>`), files, callees:
    - S_MFU_FRONT (U/Prog/mf_line_front.v): HEAD -> LONG, HDR, KEY or TAIL (empty stripped line, 0x14688).
      strchr 0x14358, strlen 0x1437c (traps 0x1436c, 0x14384, 0x14398); the comment scan 0x143c8-0x14404 (trap
      0x143e0); strip 0x14410 (trap 0x14420).
    - S_MFU_LONGP (U/Prog/mf_line_long.v): LONG -> TAIL. The blank skip 0x143a4-0x143c4, cur = NULL on '['
      (0x14690-0x146a4), m_refuse 0x146b0.
    - S_MFU_HDRA (U/Prog/mf_line_hdra.v): HDR -> HFIND or TAIL (the refusals at 0x14670, cur = NULL). memchr
      0x1443c, strip 0x14470, ieq "segment" 0x14494, strip 0x144d0 (traps 0x14448, 0x14458, 0x144a8).
    - S_MFU_HDRB (U/Prog/mf_line_hdrb.v): HFIND -> TAIL. m_find 0x144f4; found: g & 3 (0x14504), gen test, m_refuse
      0x14520, g->gen = c->gen 0x14958 (trap 0x14950); new: n < 32 (0x148dc), n++ 0x14904 (traps 0x1490c, 0x14918),
      memset 0x1492c, memcpy 0x14940, gen; full: overflow++ 0x148e8 and m_refuse 0x148f4, cur = NULL.
    - S_MFU_KEYA (U/Prog/mf_line_keya.v): KEY -> KDISP or TAIL (cur NULL or no '=': m_refuse 0x14684). memchr
      0x14530, the strips 0x14564 / 0x14570, the quotes 0x14574-0x145c4 (traps 0x1454c, 0x14588, 0x145a4, 0x145b4).
    - S_MFU_KROLE (U/Prog/mf_line_krole.v): KDISP -> KMODEL or TAIL. ieq "role" 0x145e4, fold 0x145fc (cap 64), the
      words loop 0x14618-0x1464c (strlen 0x14620, bcmp 0x14634), the role stores 0x14764 / 0x14768 (traps 0x14748,
      0x14754), snprintf 0x148b8, m_refuse 0x14658.
    - S_MFU_KMOD (U/Prog/mf_line_kmodel.v): KMODEL -> KIGN or TAIL. ieq "model" 0x146d0, fold 0x146e8 (cap 24),
      fuzz_catalogue_row 0x146f8, memcpy 0x14720 (trap 0x1470c), model_set 0x14728, m_refuse 0x147c4.
    - S_MFU_KIGNP (U/Prog/mf_line_kign.v): KIGN -> KKNOCK or TAIL. ieq "ignore" 0x1478c, ieq "yes" / "true" / "no" /
      "false" (0x147a4, 0x14830, 0x14864, 0x1487c), "1" / "0" (traps 0x14844, 0x14968), the stores 0x14898 / 0x148a0
      (trap 0x14890), snprintf 0x148b8, m_refuse 0x146b0.
    - S_MFU_KKNOCKP (U/Prog/mf_line_kign.v): KKNOCK -> TAIL. ieq "knock" 0x147dc, kept_knock[n_kept] = 1 0x14818
      (traps 0x147fc, 0x14808), m_refuse 0x146b0 (knock = true), or 0x148c8 (an unknown key). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec mfu_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c.
Import ListNotations.
Open Scope Z_scope.

Definition MFU_PC_LONG : Z := 0x143a4.
Definition MFU_PC_HDR : Z := 0x14434.
Definition MFU_PC_KEY : Z := 0x14528.
Definition MFU_PC_HFIND : Z := 0x144ec.
Definition MFU_PC_KDISP : Z := 0x145d8.
Definition MFU_PC_KMODEL : Z := 0x146c0.
Definition MFU_PC_KIGN : Z := 0x1477c.
Definition MFU_PC_KKNOCK : Z := 0x147cc.

(** The function's post from a cut: return to ra0 with sp0 and the entry s0 .. s11, the writes in M_FILE_W of the
    final model mf, and the block holding mf. *)
Definition mfu_post (ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (F : bvmap 5 word)
    (m : word -> option byte) (lo c : Z) (k0 : nat) (mf : mconf) : machine_state -> Prop :=
  ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m (M_FILE_W (bv_unsigned sp0) c k0 mf) lo
    (fun m' => mconf_at rsegs m' c mf).

(** The registers every cut inside a line keeps: s0 = c, s2 = the next line's address, s3 = the line's number, and
    the constants s7 = '#', s8 = c + 0x2000, s9 = BLANK_MASK, s10 = ' ', s11 = ';' (s4 and s6 are per cut). *)
Definition mfu_lregs (c p' line' : Z) (s0 s2 s3 s7 s8 s9 s10 s11 : word) : Prop :=
  s0 = Z_to_bv 64 c /\ s2 = Z_to_bv 64 p' /\ s3 = Z_to_bv 64 line' /\ s7 = Z_to_bv 64 0x23 /\
  s8 = Z_to_bv 64 (c + MC_N) /\ s9 = Z_to_bv 64 BLANK_MASK /\ s10 = Z_to_bv 64 0x20 /\ s11 = Z_to_bv 64 0x3b.

(** ** The cuts
    Common premises: the line-loop facts of the head (m_file_loop with the head's line number [line] and text [rest])
    of the memory at the cut, rest <> [], the bound (length rest <= n), and the loop registers with s2 = mf_next p rest
    and s3 = line + 1. *)

(** LONG: the line [p, p + |l|) has 512 bytes or more; s4 = 1, s6 = 511, s5 = p, a0 = p + |l|. *)
Definition H_MFU_LONG (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    mfu_lregs c (mf_next p rest) (line + 1) s0 s2 s3 s7 s8 s9 s10 s11 ->
    s4 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 0x1ff ->
    s5 = Z_to_bv 64 p -> a0 = Z_to_bv 64 (p + Z.of_nat (length (mf_line rest))) ->
    (512 <= length (mf_line rest))%nat ->
    evt rsegs
      (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (m_line (mc, cur) (line + 1) (mf_line rest)) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MFU_PC_LONG) fc None m (seg_rom rsegs)).

(** HDR: sl = h_strip (h_cut_comment l) = the bytes [i, j) of the line l, its first byte '['; s5 = p + i,
    s4 = p + j, a2 = j - i, s6 = 511. *)
Definition H_MFU_HDR (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z) (i j : nat),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    mfu_lregs c (mf_next p rest) (line + 1) s0 s2 s3 s7 s8 s9 s10 s11 -> s6 = Z_to_bv 64 0x1ff ->
    (length (mf_line rest) < 512)%nat ->
    (i < j)%nat -> (j <= length (mf_line rest))%nat ->
    slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)) ->
    nth i (mf_line rest) 0 = LBR ->
    s5 = Z_to_bv 64 (p + Z.of_nat i) -> s4 = Z_to_bv 64 (p + Z.of_nat j) -> a2 = Z_to_bv 64 (Z.of_nat (j - i)) ->
    evt rsegs
      (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (m_header mc (h_strip (h_cut_comment (mf_line rest))) (line + 1)) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MFU_PC_HDR) fc None m (seg_rom rsegs)).

(** KEY: as HDR, the first byte not '['. *)
Definition H_MFU_KEY (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z) (i j : nat),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    mfu_lregs c (mf_next p rest) (line + 1) s0 s2 s3 s7 s8 s9 s10 s11 -> s6 = Z_to_bv 64 0x1ff ->
    (length (mf_line rest) < 512)%nat ->
    (i < j)%nat -> (j <= length (mf_line rest))%nat ->
    slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)) ->
    nth i (mf_line rest) 0 <> LBR ->
    s5 = Z_to_bv 64 (p + Z.of_nat i) -> s4 = Z_to_bv 64 (p + Z.of_nat j) -> a2 = Z_to_bv 64 (Z.of_nat (j - i)) ->
    evt rsegs
      (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (m_key mc cur (h_strip (h_cut_comment (mf_line rest))) (line + 1), cur) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MFU_PC_KEY) fc None m (seg_rom rsegs)).

(** HFIND: the name nm = the bytes [o, o + |nm|) of the text left (inside the line), 1 <= |nm| <= 15; a1 and the cell
    0x98(sp) hold p + o, s5 = |nm|, s6 = 511. The step is mh_find. *)
Definition H_MFU_HFIND (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z) (o : nat) (nm : list Z),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    mfu_lregs c (mf_next p rest) (line + 1) s0 s2 s3 s7 s8 s9 s10 s11 -> s6 = Z_to_bv 64 0x1ff ->
    (0 < length nm < 16)%nat -> (o + length nm <= length (mf_line rest))%nat ->
    firstn (length nm) (skipn o rest) = nm ->
    a1 = Z_to_bv 64 (p + Z.of_nat o) -> cell8 m (bv_unsigned sp + 0x98) (p + Z.of_nat o) ->
    s5 = Z_to_bv 64 (Z.of_nat (length nm)) ->
    evt rsegs
      (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (mh_find mc nm (line + 1)) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MFU_PC_HFIND) fc None m (seg_rom rsegs)).

(** The key state shared by KDISP, KMODEL, KIGN and KKNOCK: cur = Some gi; the key k = the bytes [ok, ok + kl) and
    the value v = the bytes [ov, ov + vl) of the text left, both inside the line; the cell 0xa0(sp) holds p + ok,
    the cell 0x90(sp) holds p + ov, s6 = kl, s5 = vl. *)
Definition mfu_kv (rest : list Z) (ok kl ov vl : nat) (k v : list Z) : Prop :=
  (ok + kl <= length (mf_line rest))%nat /\ (ov + vl <= length (mf_line rest))%nat /\
  firstn kl (skipn ok rest) = k /\ firstn vl (skipn ov rest) = v.

(** KDISP (pc), with the words already missed [missed] (KDISP [], KMODEL [S_role], KIGN [S_role; S_model],
    KKNOCK [S_role; S_model; S_ignore]). The step is mk_disp. At KDISP a0 holds p + ok too (0x145cc), which the
    other three reload from 0xa0(sp). *)
Definition H_MFU_KAT (pc : Z) (missed : list (list Z)) (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
         (c p line : Z) (mc : mconf) (gi : nat) (k0 : nat) (rest : list Z) (ok kl ov vl : nat) (k v : list Z),
    (length rest <= n)%nat -> rest <> [] ->
    m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc (Some gi) line k0 rest
      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    mfu_lregs c (mf_next p rest) (line + 1) s0 s2 s3 s7 s8 s9 s10 s11 ->
    s6 = Z_to_bv 64 (Z.of_nat kl) -> s5 = Z_to_bv 64 (Z.of_nat vl) ->
    cell8 m (bv_unsigned sp + 0xa0) (p + Z.of_nat ok) -> cell8 m (bv_unsigned sp + 0x90) (p + Z.of_nat ov) ->
    (pc = MFU_PC_KDISP -> a0 = Z_to_bv 64 (p + Z.of_nat ok)) ->
    mfu_kv rest ok kl ov vl k v ->
    Forall (fun w => ieq k w = false) missed ->
    evt rsegs
      (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
         (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Definition H_MFU_KDISP (n : nat) : Prop := H_MFU_KAT MFU_PC_KDISP [] n.
Definition H_MFU_KMODEL (n : nat) : Prop := H_MFU_KAT MFU_PC_KMODEL [S_role] n.
Definition H_MFU_KIGN (n : nat) : Prop := H_MFU_KAT MFU_PC_KIGN [S_role; S_model] n.
Definition H_MFU_KKNOCK (n : nat) : Prop := H_MFU_KAT MFU_PC_KKNOCK [S_role; S_model; S_ignore] n.

(** ** The sub-pieces of S_MF_LINE *)
Definition S_MFU_FRONT : Prop :=
  forall n, H_MF_TAIL n -> H_MFU_LONG n -> H_MFU_HDR n -> H_MFU_KEY n -> H_MF_HEAD (S n).
Definition S_MFU_LONGP : Prop := forall n, H_MF_TAIL n -> H_MFU_LONG n.
Definition S_MFU_HDRA : Prop := forall n, H_MF_TAIL n -> H_MFU_HFIND n -> H_MFU_HDR n.
Definition S_MFU_HDRB : Prop := forall n, H_MF_TAIL n -> H_MFU_HFIND n.
Definition S_MFU_KEYA : Prop := forall n, H_MF_TAIL n -> H_MFU_KDISP n -> H_MFU_KEY n.
Definition S_MFU_KROLE : Prop := forall n, H_MF_TAIL n -> H_MFU_KMODEL n -> H_MFU_KDISP n.
Definition S_MFU_KMOD : Prop := forall n, H_MF_TAIL n -> H_MFU_KIGN n -> H_MFU_KMODEL n.
Definition S_MFU_KIGNP : Prop := forall n, H_MF_TAIL n -> H_MFU_KKNOCK n -> H_MFU_KIGN n.
Definition S_MFU_KKNOCKP : Prop := forall n, H_MF_TAIL n -> H_MFU_KKNOCK n.

Lemma mfu_line_from_parts :
  S_MFU_FRONT -> S_MFU_LONGP -> S_MFU_HDRA -> S_MFU_HDRB -> S_MFU_KEYA -> S_MFU_KROLE -> S_MFU_KMOD ->
  S_MFU_KIGNP -> S_MFU_KKNOCKP -> S_MF_LINE.
Proof.
  intros FR LG HA HB KA KR KM KI KK n HT.
  pose proof (KK n HT) as HKK. pose proof (KI n HT HKK) as HKI. pose proof (KM n HT HKI) as HKM.
  pose proof (KR n HT HKM) as HKD. pose proof (KA n HT HKD) as HKY.
  pose proof (HB n HT) as HHF. pose proof (HA n HT HHF) as HHD.
  exact (FR n HT (LG n HT) HHD HKY).
Qed.
