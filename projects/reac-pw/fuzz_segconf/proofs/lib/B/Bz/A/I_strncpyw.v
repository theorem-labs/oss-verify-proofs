(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan sha256 c0661b96). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strcpyw.v, with its module paths, addresses and numbers changed; 533 of its 721 lines of code are new or changed and 259 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Bz/A/I_strncpyw.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The strncpy wrapper of reac-pw/fuzz_segconf's ASan+UBSan image B (0x4b188, 1328 B), walked in the Bz kit:
   AsanInitFromRtl, the flag byte asan_flags + 0x1d, REAL(strnlen) = musl strnlen 0x9b634 (which calls the memchr
   wrapper), from_size := min(n, strnlen(s, n) + 1), the overlap check of [d, d + from_size) and [s, s + from_size),
   the range checks of from_size bytes at s and of n bytes at d, REAL(strncpy) = musl strncpy 0x9b4fc (the Section
   hypothesis SNC, stated in I_ncpyspec.v), return. The control flow follows
   proofs/pupnp/FuzzHttp/lib/A0/ICP/I_strncpy.v strncpy_i_spec (origin/ossv/recipes); the check lemmas follow the
   memset and memcpy wrapper walks of this tree (I_imemset.v, I_memcpyw.v, I_memcpyw2.v). For n = 0 the walk holds
   no fact on the bytes at s and d: musl strnlen(s, 0) goes through the memchr wrapper's size-0 path. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec D_kit I_ikit I_init I_musl I_memchrw I_strnlenw I_memsetw I_ncpyspec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* Hide the memory facts that do not name the frame while the prologue stores run; transport them once after. *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Definition i_strncpy : Z := 0x4b188.
Notation ISTRNCPY_DEPTH := 4416%Z (only parsing).   (* 2160 frame + max(2240 strnlen, 2256 strncpy, 80, 16) *)
Definition icells_ncpy (m : mem) : Prop :=
  ro_cells asegs m 0xa3208 [C8 (Z_to_bv 64 0xa9fb8)]      (* .got -> asan_flags_dont_use_directly *)
  /\ ro_cells asegs m 0xa9fd5 [C1 (Z_to_bv 8 1)]          (* asan_flags + 0x1d *)
  /\ ro_cells asegs m 0xa5050 [C8 (Z_to_bv 64 0x9b634)]   (* REAL(strnlen) = musl strnlen *)
  /\ ro_cells asegs m 0xa5070 [C8 (Z_to_bv 64 0x9b4fc)].  (* REAL(strncpy) = musl strncpy *)
Definition isncpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d n : Z) (str : list byte) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' d [CB (Z.to_nat n) (stpn_result str (Z.to_nat n))].

(* ---- Facts without a walk ---- *)

Lemma bytes_at_nil : forall (m : mem) a, 0 <= a <= 2^64 -> bytes_at asegs m a [].
Proof. intros m a Ha. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. Qed.

(* An empty cell is a fact about no byte: it holds in every memory. *)
Lemma rw_cells_CB0 : forall (m m' : mem) a junk, rw_cells asegs m a [CB 0 junk] -> rw_cells asegs m' a [CB 0 junk].
Proof.
  intros m m' a junk ((WF & B0 & B1 & _) & W0 & W1 & _).
  destruct WF as [WF _]. cbn [cell_wf] in WF. destruct junk as [|b junk]; [| cbn in WF; discriminate].
  split; [split|].
  - split; [reflexivity| exact I].
  - split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. cbn in Hi. lia.
Qed.

Lemma chk_ok_zero : forall (m : mem) p, chk_ok m p 0.
Proof. intros m p. split; [intros i Hi; lia|]. split; [intros Hn; lia| intros Hn; lia]. Qed.

Lemma chk_tails_zero : forall (m : mem) d, chk_tails m d 0.
Proof. intros m d i Hi. replace (0 - i) with 0 by lia. apply chk_ok_zero. Qed.

Lemma chk_tails_agree : forall (m m' : mem) d n, chk_tails m d n -> 0 <= d -> d + n <= 2^47 ->
  agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m m' -> chk_tails m' d n.
Proof. intros m m' d n CT D0 DH AG i Hi. apply (chk_ok_agree m m' (d + i) (n - i) (CT i Hi)); [lia| lia| exact AG]. Qed.

Lemma memchr_res_nil : forall A c n, memchr_res A c n [] = 0.
Proof. intros. unfold memchr_res. rewrite firstn_nil. reflexivity. Qed.

Lemma memchr_ok_nil : forall A c, memchr_ok A c 0 [].
Proof. intros. unfold memchr_ok. rewrite firstn_nil. cbn [find_byte]. lia. Qed.

Lemma m2s_agree : forall (m m' : mem), m2s_cells m -> agree_on (fun x => 0 <= x < 0x1000000) m m' -> wmono asegs m m' ->
  m2s_cells m'.
Proof.
  intros m m' (C1 & C2 & C3) AG WM.
  split; [| split].
  - apply (rw_cells_agree asegs m m' _ _ C1); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree asegs m m' _ _ C2); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree asegs m m' _ _ C3); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
Qed.

Lemma icells_mc_agree : forall (m m' : mem), icells_mc m -> agree_on (fun x => 0 <= x < 0x1000000) m m' -> wmono asegs m m' ->
  icells_mc m'.
Proof.
  intros m m' (C1 & C2 & C3 & C4) AG WM.
  split; [| split; [| split]].
  - apply (ro_cells_agree asegs m m' _ _ C1). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C2). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree asegs m m' _ _ C4); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
Qed.

Lemma icells_ms_agree : forall (m m' : mem), icells_ms m -> agree_on (fun x => 0 <= x < 0x1000000) m m' -> icells_ms m'.
Proof.
  intros m m' (C1 & C2 & C3 & C4 & C5) AG.
  split; [| split; [| split; [| split]]].
  - apply (ro_cells_agree asegs m m' _ _ C1). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C2). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C4). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C5). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
Qed.

Lemma find_byte_nonul : forall (str : list byte) k, ~ In (Z_to_bv 8 0) str -> find_byte 0 (firstn k str) = None.
Proof.
  intros str k NZ. apply find_byte_notin. intros b Hb E. apply NZ.
  replace (Z_to_bv 8 0) with b; [rewrite <- (firstn_skipn k str); apply in_or_app; left; exact Hb|].
  apply bv_eq. rewrite E. reflexivity.
Qed.

(* What musl strnlen(s, n) reads and returns on the source of ncpy_src, and the size the wrapper checks at s. *)
Lemma ncpy_src_facts : forall s n str src, 0 <= n -> ncpy_src s (Z.to_nat n) str src ->
  ~ In (Z_to_bv 8 0) str /\ memchr_ok s 0 n src /\ memchr_chk 0 n src = Z.min n (Z.of_nat (length str) + 1) /\
  strnlen_res n src = Z.min (Z.of_nat (length str)) n /\ Z.min n (Z.of_nat (length str) + 1) <= Z.of_nat (length src).
Proof.
  intros s n str src N0 (NZ & [(slack & -> & PAD) | (Hn & ->)]).
  - split; [exact NZ|]. split; [apply memchr_ok_cstr; assumption|].
    rewrite length_app. cbn [length].
    unfold memchr_chk, strnlen_res.
    destruct (Z.lt_ge_cases (Z.of_nat (length str)) n) as [H|H].
    + rewrite find_byte_cstr by assumption. cbv beta iota. lia.
    + rewrite find_byte_cstr_short by assumption. cbv beta iota. lia.
  - split; [exact NZ|].
    unfold memchr_ok, memchr_chk, strnlen_res. rewrite firstn_firstn, Nat.min_id, find_byte_nonul by exact NZ.
    cbv beta iota. rewrite length_firstn. lia.
Qed.

(* ---- The byte loops of the two quick checks (shadow bytes from a0 up to a1, or-ed into a2) ---- *)

Lemma isncpy_loopS : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4b4dc) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b4cc) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Lemma isncpy_loopD : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4b5a4) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b594) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

(* The overlap check of [d, d + f) and [s, s + f) (0x4b208 .. 0x4b21c): it passes when the two are apart. *)
Lemma isncpy_ovl : forall (sp d s f : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  0 <= s -> 0 <= d -> 0 <= f -> s + f < 2^63 -> d + f < 2^63 -> 0 <= sp < 2^63 -> (d + f <= s \/ s + f <= d) ->
  evt asegs (fun ms' => exists (a0' s8' : word),
      ms' = MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1 a0' a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 f) (Z_to_bv 64 (s + f)) s6 s7 s8' s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4b220) fc None m (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 f) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b208) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros S0 D0 F0 SF DF SP OV.
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUsf : bv_unsigned (Z_to_bv 64 (s + f)) = s + f) by (apply unsigned_lit; lia).
  assert (EUdf : bv_unsigned (Z_to_bv 64 (d + f)) = d + f) by (apply unsigned_lit; lia).
  do 4 lstep. lstep. if_cases KO; zify_cond KO.
  - apply evt_done. do 2 eexists. reflexivity.
  - lstep. if_false. apply evt_done. do 2 eexists. reflexivity.
Qed.

Definition chkS_post (sp p L : Z) (gp tp s0 s1 s3 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2160)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 p) s3 (Z_to_bv 64 L) s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x4b26c) fc None m' (seg_rom asegs)
    /\ munch [(sp - 2240, sp - 2160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2160).

Definition chkD_post (sp : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2160)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x4b2bc) fc None m' (seg_rom asegs)
    /\ munch [(sp - 2240, sp - 2160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2160).

Section WithRIP.
Hypothesis RIP : rip_stmt.          (* I_consts.v: the range check 0x58724 *)
Hypothesis MCH : memchr_stmt.       (* I_musl.v: musl memchr, under the memchr wrapper *)
Hypothesis SNC : strncpyA_stmt.     (* I_ncpyspec.v: musl strncpy, REAL(strncpy) *)

(* ---- strnlen(s, 0): musl strnlen, the memchr wrapper's size-0 path and musl memchr, with no fact on s's bytes ---- *)

Lemma imemchr_zero : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s cz : Z) (lo : Z),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 cz -> a2 = Z_to_bv 64 0 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - IMEMCHR_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 <= s <= 2^47 -> 0 <= cz < 2^64 ->
  m2s_cells m -> icells_mc m -> mem_inv asegs m ->
  evt asegs (imemchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46fc8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO SPH S0 HC M2S IC MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2208, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (G2 & RM & SHC & AI).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EU2128 : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
  carve_frame 56%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  do 14 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. lstep.
  call try_init_spec; [exact AI| rewrite EU2128; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2128 in H; rename H into ST2 end.
  do 7 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (bytes_at_nil mm s ltac:(lia)) as BUF end.
  call MCH; [rewrite EUs; exact BUF| rewrite (unsigned_lit 0) by lia; apply memchr_ok_nil| assumption|].
  rewrite memchr_res_nil.
  lstep. if_false.
  lstep. if_false.
  do 3 lstep. lstep. rewrite (lxor_ones64 s) by lia.
  assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - s)) = 18446744073709551615 - s) by (apply unsigned_lit; lia).
  if_false.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (chk_ok_zero mm s) as CS1;
    assert (M2S1 : m2s_cells mm)
      by (apply (m2s_agree m mm M2S); [apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; lia| exact WM]);
    assert (IC1 : icells_mc mm) by (split; [exact G2| split; [exact RM| split; [exact SHC| exact AI]]])
  end.
  call (imemchr_chk RIP usp s 0); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia
        | exact CS1| exact M2S1| exact IC1| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2128) |- _ => rename H into ST3 end.
  do 9 lstep.
  release_frame FR ST3 (usp + -56). release_frame FRs ST3 usp.
  lstep.
  unfold imemchr_post. sys_finish.
  + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite EU. assumption.
Qed.

Lemma mstrnlen_zero : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z) (lo : Z),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 0 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNLEN_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 <= s <= 2^47 -> m2s_cells m -> icells_mc m -> mem_inv asegs m ->
  evt asegs (mstrnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9b634) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> ST LO LOLO SPH S0 M2S IC MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2240, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  do 10 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm)
      by (apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_agree m mm M2S AGL WM) as M2S1;
    pose proof (icells_mc_agree m mm IC AGL WM) as IC1;
    clear AGL
  end.
  call imemchr_zero; [reflexivity| reflexivity| reflexivity| rewrite EU32; exact ST| lia
        | unfold kHighShadowEnd; lia| lia| lia| lia| exact M2S1| exact IC1| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU32 in H; rename H into ST1 end.
  lstep. if_true.
  do 5 lstep. release_frame FR ST1 usp. lstep.
  unfold mstrnlen_post. sys_finish.
  + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite EU. assumption.
Qed.

(* ---- The range check of a source run (0x4b220 .. 0x4b268, 0x4b430, 0x4b4b0 .. 0x4b4f0) ---- *)

Lemma isncpy_ripS : forall (sp p L : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2160) -> lo <= sp - 2240 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 < L -> p + L < 2^63 ->
  acc asegs m p L -> rng_ok p L -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chkS_post sp p L gp tp s0 s1 s3 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 (Z_to_bv 64 L) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b4e4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2160)) = sp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold chkS_post. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma isncpy_chkS : forall (sp p L : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2160) -> lo <= sp - 2240 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L < 2^63 ->
  chk_ok m p L -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chkS_post sp p L gp tp s0 s1 s3 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 (Z_to_bv 64 L) (Z_to_bv 64 (p + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b220) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (M2S : m2s_cells m) by (split; [exact G2| split; [exact SHC| exact HM]]). unfold SHB in SHC.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EUpL : bv_unsigned (Z_to_bv 64 (p + L)) = p + L) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  if_false.
  lstep. lstep. lstep.
  destruct (Z_lt_le_dec 64 L) as [BIG|SMALL]; [| destruct (Z.eq_dec L 0) as [Z0|NZ]].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (L + -65)) = L - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (isncpy_ripS sp p L); try assumption; lia.
  - subst L. if_true. lstep. if_false. lstep.
    apply evt_done. unfold chkS_post. do 18 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (L + -65)) = L - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 10 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + L + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + L - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + L + -1) with (p + L - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + L + -1) / 8) with ((p + L + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p L AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + L + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chkS_post. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isncpy_ripS sp p L); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (isncpy_loopS (Z.to_nat ((p + L + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chkS_post. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isncpy_ripS sp p L); try assumption; lia.
    + apply evt_done. unfold chkS_post. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

(* ---- The range check of the destination run (0x4b26c .. 0x4b2b8, 0x4b4a8, 0x4b578 .. 0x4b5b8) ---- *)

Lemma isncpy_ripD : forall (sp p L : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2160) -> lo <= sp - 2240 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 < L -> p + L < 2^63 ->
  acc asegs m p L -> rng_ok p L -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chkD_post sp gp tp s0 (Z_to_bv 64 L) s2 (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 L) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b5ac) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2160)) = sp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold chkD_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma isncpy_chkD : forall (sp p L : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2160) -> lo <= sp - 2240 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L < 2^63 ->
  chk_ok m p L -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chkD_post sp gp tp s0 (Z_to_bv 64 L) s2 (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 L) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b26c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (M2S : m2s_cells m) by (split; [exact G2| split; [exact SHC| exact HM]]). unfold SHB in SHC.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  if_false.
  lstep. lstep. lstep.
  destruct (Z_lt_le_dec 64 L) as [BIG|SMALL]; [| destruct (Z.eq_dec L 0) as [Z0|NZ]].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (L + -65)) = L - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (isncpy_ripD sp p L); try assumption; lia.
  - subst L. if_true. lstep. if_false. lstep.
    apply evt_done. unfold chkD_post. do 17 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (L + -65)) = L - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + L + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + L - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + L + -1) with (p + L - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + L + -1) / 8) with ((p + L + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p L AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + L + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chkD_post. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isncpy_ripD sp p L); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (isncpy_loopD (Z.to_nat ((p + L + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chkD_post. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isncpy_ripD sp p L); try assumption; lia.
    + apply evt_done. unfold chkD_post. do 17 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

(* ---- From from_size (0x4b208) to the return: the overlap check, the two range checks, REAL(strncpy), the
   epilogue. The facts are those of the current memory m; the frame cells hold the saved registers. ---- *)

Lemma isncpy_back : forall (sp d s n f lo : Z) (str src junk fjunk : list byte)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 : word) F fc (m : mem),
  stk asegs m lo (sp + -2160) -> lo <= sp - ISTRNCPY_DEPTH -> kHighShadowEnd < lo -> sp <= 2^47 ->
  0 < s -> 0 <= d -> 0 <= n < 2^32 -> s + Z.of_nat (length src) <= 2^47 -> d + n <= 2^47 ->
  f = Z.min n (Z.of_nat (length str) + 1) -> f <= Z.of_nat (length src) ->
  bytes_at asegs m s src -> ncpy_src s (Z.to_nat n) str src ->
  rw_cells asegs m d [CB (Z.to_nat n) junk] ->
  (d + n <= s \/ s + Z.of_nat (length src) <= d) ->
  (n = 0 \/ s + Z.of_nat (length src) <= lo \/ sp <= s) ->
  (n = 0 \/ d + n <= lo \/ sp <= d) ->
  chk_ok m s (Z.min n (Z.of_nat (length str) + 1)) -> chk_tails m d n -> ncpy_cells_apart d n ->
  m2s_cells m -> icells_ms m -> ro_cells asegs m 0xa5070 [C8 (Z_to_bv 64 0x9b4fc)] -> mem_inv asegs m ->
  rw_cells asegs m (sp + -80) [C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells asegs m (sp + -2160) [CB 2080 fjunk] ->
  evt asegs (isncpy_post vra (Z_to_bv 64 sp) gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 s9 s10 s11 F fc d n str
                 [(d, d + n); (sp - ISTRNCPY_DEPTH, sp)] lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 f) s5 s6 (Z_to_bv 64 0xa5050) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b208) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO LOLO SPH S0 D0 N0 SH DH EF FL SRC NS DST OV SEPS SEPD CS CT CA M2S ICS RSC MI FRs FR.
  unfold kHighShadowEnd in *. rewrite <- EF in CS.
  assert (F0 : 0 <= f <= n) by lia.
  pose proof (munch_refl [(d, d + n); (sp - 4416, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(sp - 4416, sp)] m) as MUs.
  assert (EUsp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (sp + -2160)) = sp + -2160) by (apply unsigned_lit; lia).
  change (keep (bytes_at asegs m s src)) in SRC. change (keep (rw_cells asegs m d [CB (Z.to_nat n) junk])) in DST.
  change (keep (d + n <= s \/ s + Z.of_nat (length src) <= d)) in OV.
  change (keep (n = 0 \/ s + Z.of_nat (length src) <= lo \/ sp <= s)) in SEPS.
  change (keep (n = 0 \/ d + n <= lo \/ sp <= d)) in SEPD.
  change (keep (ncpy_src s (Z.to_nat n) str src)) in NS.
  eapply evt_cut; [eapply (isncpy_ovl sp d s f); unfold keep in OV; lia|].
  intros ms' (a0' & s8' & ->).
  (* the source run *)
  call (isncpy_chkS sp s f); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CS| exact M2S| exact MI|].
  lazymatch goal with H : stk asegs _ lo (sp + -2160) |- _ => rename H into ST1 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm)
      by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm)
      by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (CD1 : chk_ok mm d n)
      by (pose proof (CT 0 ltac:(lia)) as C0; rewrite Z.add_0_r, Z.sub_0_r in C0; exact (chk_ok_agree m mm d n C0 D0 DH AGS));
    pose proof (m2s_agree m mm M2S AGL WM) as M2S1;
    clear AGS AGL
  end.
  (* the destination run *)
  call (isncpy_chkD sp d n); [exact ST1| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CD1| exact M2S1| assumption|].
  lazymatch goal with H : stk asegs _ lo (sp + -2160) |- _ => rename H into ST2 end.
  clear CD1 M2S1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm)
      by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm)
      by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_agree m mm M2S AGL WM) as M2S2;
    pose proof (icells_ms_agree m mm ICS AGL) as ICS2;
    pose proof (chk_tails_agree m mm d n CT D0 DH AGS) as CT2;
    clear AGS AGL
  end.
  (* REAL(strncpy) *)
  do 5 lstep.
  pose proof SNC as SNCs. unfold strncpyA_stmt in SNCs.
  unfold keep in OV, NS.
  destruct (Z.eq_dec n 0) as [NZ0|NNZ].
  - (* n = 0: no byte at s or d is copied or checked *)
    subst n.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bytes_at_nil mm s ltac:(lia)) as SRC2;
      pose proof (rw_cells_CB0 m mm d junk DST) as DST2
    end.
    assert (NS2 : ncpy_src s (Z.to_nat 0) str []) by (split; [exact (proj1 NS)| right; split; [cbn; lia| reflexivity]]).
    clear MUs.
    eapply evt_cut; [ eapply SNCs with (str := str) (src := []) (junk := junk) (lo := lo);
      [reflexivity| reflexivity| reflexivity| rewrite EU2160; exact ST2| lia| unfold kHighShadowEnd; lia| lia
      | lia| lia| lia| cbn [length]; lia| lia| exact SRC2| exact NS2| exact DST2| cbn [length]; lia| left; reflexivity| left; reflexivity
      | exact CT2| exact CA| exact M2S2| exact ICS2| assumption] |].
    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
    lazymatch type of MUc with munch _ ?m1 ?m2 =>
      assert (MUe : munch [(sp - 4416, sp - 2160)] m1 m2)
        by (eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia);
      clear MUc; transport_after_call asegs m1 m2 MUe WMc; clear MUe WMc end.
    destruct_ands PO.
    replace (ret_pc (Z_to_bv 64 0x4b2d0)) with (Z_to_bv 64 0x4b2d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite EU2160 in *.
    lazymatch goal with H : stk asegs _ lo (sp + -2160) |- _ => rename H into ST3 end.
    do 11 lstep. release_frame FR ST3 (sp + -80). release_frame FRs ST3 sp. lstep. lstep.
    unfold isncpy_post. sys_finish. all: rewrite ?EUsp; assumption.
  - (* n > 0: s and d lie apart from the frames *)
    unfold keep in SEPS, SEPD.
    assert (SEPS' : s + Z.of_nat (length src) <= lo \/ sp <= s) by lia.
    assert (SEPD' : d + n <= lo \/ sp <= d) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SRC2 : bytes_at asegs mm s src)
        by (unfold keep in SRC; apply (bytes_at_transport asegs _ m mm _ _ SRC MUs); cbn [disjoint_from]; lia);
      assert (DST2 : rw_cells asegs mm d [CB (Z.to_nat n) junk])
        by (unfold keep in DST; apply (rw_cells_transport asegs _ m mm _ _ DST MUs WM); cbn [disjoint_from cells_size csize]; lia)
    end.
    clear MUs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply SNCs with (str := str) (src := src) (junk := junk) (lo := lo);
      [reflexivity| reflexivity| reflexivity| rewrite EU2160; exact ST2| lia| unfold kHighShadowEnd; lia| lia
      | lia| lia| lia| lia| lia| exact SRC2| exact NS| exact DST2| exact OV| lia| lia
      | exact CT2| exact CA| exact M2S2| exact ICS2| assumption]
    | post_call asegs mm ] end.
    rewrite EU2160 in *.
    lazymatch goal with H : stk asegs _ lo (sp + -2160) |- _ => rename H into ST3 end.
    do 11 lstep. release_frame FR ST3 (sp + -80). release_frame FRs ST3 sp. lstep. lstep.
    unfold isncpy_post. sys_finish. all: rewrite ?EUsp; assumption.
Qed.

Local Ltac ncpy_agree m MUs AGL AGS :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm)
      by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm)
      by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia)
  end.

Theorem isncpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d s n : Z) (str src junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNCPY_DEPTH -> kHighShadowEnd < lo ->
  bv_unsigned sp <= 2^47 ->
  0 < s -> 0 <= d -> 0 <= n < 2^32 -> s + Z.of_nat (length src) <= 2^47 -> d + n <= 2^47 ->
  bytes_at asegs m s src -> ncpy_src s (Z.to_nat n) str src ->
  rw_cells asegs m d [CB (Z.to_nat n) junk] ->
  (d + n <= s \/ s + Z.of_nat (length src) <= d) ->
  (n = 0 \/ s + Z.of_nat (length src) <= lo \/ bv_unsigned sp <= s) ->
  (n = 0 \/ d + n <= lo \/ bv_unsigned sp <= d) ->
  chk_ok m s (Z.min n (Z.of_nat (length str) + 1)) -> chk_tails m d n -> ncpy_cells_apart d n ->
  m2s_cells m -> rw_cells asegs m 0xad498 [C1 (Z_to_bv 8 1)] -> icells_ncpy m -> icells_mc m -> icells_ms m ->
  mem_inv asegs m ->
  evt asegs (isncpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d n str
                 [(d, d + n); (bv_unsigned sp - ISTRNCPY_DEPTH, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 i_strncpy) fc None m (seg_rom asegs)).
Proof using RIP MCH SNC.
  intros until lo. intros -> -> -> ST LO LOLO SPH S0 D0 N0 SH DH SRC NS DST OV SEPS SEPD CS CT CA M2S AI ICN ICM ICS MI.
  unfold kHighShadowEnd, i_strncpy in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  destruct (ncpy_src_facts s n str src ltac:(lia) NS) as (NZ & MOK & MCK & SNR & FSL).
  pose proof ICN as (GFL & FLG & RSN & RSC).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(d, d + n); (usp - 4416, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(usp - 4416, usp)] m) as MUs.
  change (keep (bytes_at asegs m s src)) in SRC. change (keep (rw_cells asegs m d [CB (Z.to_nat n) junk])) in DST.
  change (keep (d + n <= s \/ s + Z.of_nat (length src) <= d)) in OV.
  change (keep (n = 0 \/ s + Z.of_nat (length src) <= lo \/ usp <= s)) in SEPS.
  change (keep (n = 0 \/ d + n <= lo \/ usp <= d)) in SEPD.
  change (keep (ncpy_src s (Z.to_nat n) str src)) in NS.
  (* prologue: the 2160-byte frame, the saves of ra and s0 .. s8 at its top *)
  carve_frame 80%nat ST. rename FR into FRs. carve_frame 2080%nat ST.
  zidle_beginz usp 2160%Z MUz1 WMz1.
  do 17 lstep.
  zidle_end MUz1 WMz1.
  (* AsanInitFromRtl *)
  call asan_init_spec; [exact AI| rewrite EU2160; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2160 in H; rename H into ST1 end.
  (* the flag byte, REAL(strnlen), the call *)
  xsteps_to 0x9b634%Z.
  destruct (Z.eq_dec n 0) as [NZ0|NNZ].
  - (* n = 0 *)
    subst n.
    ncpy_agree m MUs AGL AGS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (m2s_agree m mm M2S AGL WM) as M2S1;
      pose proof (icells_mc_agree m mm ICM AGL WM) as IC1
    end.
    clear AGL AGS.
    call mstrnlen_zero; [reflexivity| reflexivity| rewrite EU2160; exact ST1| lia| unfold kHighShadowEnd; lia| lia| lia
          | exact M2S1| exact IC1| assumption|].
    lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2160 in H; rename H into ST2 end.
    clear M2S1 IC1.
    assert (EU01 : bv_unsigned (Z_to_bv 64 (0 + 1)) = 1) by (apply unsigned_lit; lia).
    xsteps_to 0x4b208%Z.
    ncpy_agree m MUs AGL AGS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (m2s_agree m mm M2S AGL WM) as M2S2;
      pose proof (icells_ms_agree m mm ICS AGL) as ICS2;
      pose proof (bytes_at_nil mm s ltac:(lia)) as SRC2;
      pose proof (rw_cells_CB0 m mm d junk DST) as DST2
    end.
    clear AGL AGS MUs.
    unfold keep in NS.
    call (isncpy_back usp d s 0 0 lo str [] junk); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia
          | cbn [length]; lia| lia| lia| cbn [length]; lia
          | exact SRC2| split; [exact NZ| right; split; [cbn; lia| reflexivity]]| exact DST2| cbn [length]; lia
          | left; reflexivity| left; reflexivity
          | replace (Z.min 0 (Z.of_nat (length str) + 1)) with 0 by lia; apply chk_ok_zero| apply chk_tails_zero| exact CA
          | exact M2S2| exact ICS2| exact RSC| assumption| exact FRs| exact FR|].
    unfold isncpy_post. sys_finish.
  - (* n > 0 *)
    unfold keep in SEPS, SEPD.
    assert (SEPS' : s + Z.of_nat (length src) <= lo \/ usp <= s) by lia.
    assert (SEPD' : d + n <= lo \/ usp <= d) by lia.
    clear SEPS SEPD.
    ncpy_agree m MUs AGL AGS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (m2s_agree m mm M2S AGL WM) as M2S1;
      pose proof (icells_mc_agree m mm ICM AGL WM) as IC1;
      assert (CS1 : chk_ok mm s (memchr_chk 0 n src)) by (rewrite MCK; exact (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia) AGS));
      assert (SRC1 : bytes_at asegs mm s src)
        by (unfold keep in SRC; apply (bytes_at_transport asegs _ m mm _ _ SRC MUs); cbn [disjoint_from]; lia)
    end.
    clear AGL AGS.
    call (musl_strnlen_spec RIP MCH); [reflexivity| reflexivity| rewrite EU2160; exact ST1| lia| unfold kHighShadowEnd; lia| lia| lia| lia
          | rewrite MCK; lia| exact SRC1| exact MOK| lia| exact CS1| exact M2S1| exact IC1| assumption|].
    lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2160 in H; rename H into ST2 end.
    clear CS1 M2S1 IC1.
    try clear SRC1.
    rewrite SNR.
    remember (Z.min (Z.of_nat (length str)) n) as r eqn:Er.
    assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
    ncpy_agree m MUs AGL AGS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (m2s_agree m mm M2S AGL WM) as M2S2;
      pose proof (icells_ms_agree m mm ICS AGL) as ICS2;
      pose proof (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia) AGS) as CS2;
      pose proof (chk_tails_agree m mm d n CT ltac:(lia) ltac:(lia) AGS) as CT2;
      assert (SRC2 : bytes_at asegs mm s src)
        by (unfold keep in SRC; apply (bytes_at_transport asegs _ m mm _ _ SRC MUs); cbn [disjoint_from]; lia);
      assert (DST2 : rw_cells asegs mm d [CB (Z.to_nat n) junk])
        by (unfold keep in DST; apply (rw_cells_transport asegs _ m mm _ _ DST MUs WM); cbn [disjoint_from cells_size csize]; lia)
    end.
    clear AGL AGS MUs.
    unfold keep in OV, NS.
    lstep. lstep. lstep. if_cases KM; zify_cond KM; rewrite ?EUn, ?EUr1 in KM.
    + (* n < strnlen + 1: from_size = n *)
      call (isncpy_back usp d s n n lo str src junk); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia| lia| lia
            | exact SRC2| exact NS| exact DST2| exact OV| lia| lia| exact CS2| exact CT2| exact CA| exact M2S2| exact ICS2| exact RSC
            | assumption| exact FRs| exact FR|].
      unfold isncpy_post. sys_finish.
    + (* from_size = strnlen + 1 *)
      lstep.
      call (isncpy_back usp d s n (r + 1) lo str src junk); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia| lia| lia
            | exact SRC2| exact NS| exact DST2| exact OV| lia| lia| exact CS2| exact CT2| exact CA| exact M2S2| exact ICS2| exact RSC
            | assumption| exact FRs| exact FR|].
      unfold isncpy_post. sys_finish.
Qed.

End WithRIP.
