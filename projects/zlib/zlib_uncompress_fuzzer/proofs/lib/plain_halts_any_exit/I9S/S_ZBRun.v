(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase S_Entry S_ZA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require RefMemcpyLib FuzzMem S9MemcpyBase S9Memcpy S9AdlerBase S9AdlerIface S9Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require S9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_It3.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZBI. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZBI.




From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZStep.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZBF. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZBF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.







Module S_Tok.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Frame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Hoare.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.FuzzMem OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9MemcpyBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9Memcpy OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9AdlerBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9AdlerIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9Adler.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9LibStmt.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_LeaveA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.S_U2A OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2B OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2C S_It7 S_Fast1 S_Fast7.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.


Lemma w64_lit : forall z (w : word), bv_unsigned w = z -> w64 z = w.
Proof. intros z w <-. apply w64_of_word. Qed.

(* the goal's `w64` of a named constant is replaced by a word that the handed-in application determines;
   the equation between the two is closed by computation *)
Local Ltac w64_as_word a tac :=
  let W := fresh "W" in
  evar (W : word);
  replace (w64 a) with W;
  [ unfold W; clear W; tac
  | unfold W; clear W; first [ apply w64_lit; reflexivity | symmetry; apply w64_lit; reflexivity ] ].

Lemma msteps_memcpy_S9 {RCa1 : RunCtx}  : msteps_memcpy (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMCPY.
Proof.
  intros mem0 dst src n bs rom Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd regs ret Hret H1 H10 H11 H12.
  w64_as_word A_MEMCPY ltac:(apply (ref_memcpy mem0 dst src n bs rom); try assumption; constructor; assumption).
Qed.
Theorem memcpy_ok {RCa1 : RunCtx}  : memcpy_spec_s.
Proof. unfold memcpy_spec_s. apply memcpy_glue. apply msteps_memcpy_S9. Qed.

Lemma img_ok_of_rom_ok : forall m, rom_ok m -> img_ok m.
Proof.
  intros m H. apply (img_ok_of_range m ROM_LO ROM_HI).
  - apply rom_hyp_of_okG; [cbv [ROM_LO]; lia_std | rewrite two64_eq; cbv [ROM_HI]; lia_std | exact H].
  - cbv [ROM_LO RO_LO]. lia_std.
  - cbv [ROM_HI RO_HI]. lia_std.
Qed.
Lemma msteps_adler32_S9 {RCa1 : RunCtx}  : msteps_adler32 (run_segments R_segs rc_inp rc_sp rc_mb) A_ADLER32 FR_AD rom_ok.
Proof.
  intros regs m rom retw usp a adr v len. unfold FR_AD.
  w64_as_word A_ADLER32 ltac:(intros; eapply (s9_adler32 regs m rom retw usp a adr v len); try eassumption; apply img_ok_of_rom_ok; assumption).
Qed.
Theorem adler32_ok {RCa1 : RunCtx}  : adler32_spec_s.
Proof. unfold adler32_spec_s. apply adler32_glue; [cbv [FR_AD]; lia_std | apply msteps_adler32_S9]. Qed.

Lemma msteps_adler32_null_S9 {RCa1 : RunCtx}  : msteps_adler32_null0 (run_segments R_segs rc_inp rc_sp rc_mb) A_ADLER32.
Proof.
  intros regs m rom retw.
  w64_as_word A_ADLER32 ltac:(exact (s9_adler32_null regs m rom retw)).
Qed.
Theorem adler32_null_ok {RCa1 : RunCtx}  : adler32_null_spec_s.
Proof. unfold adler32_null_spec_s. apply adler32_null0_glue. apply msteps_adler32_null_S9. Qed.

Theorem itable_ok {RCa1 : RunCtx}  : itable_spec_s.
Proof. exact itable_s. Qed.
Theorem ifast_ok {RCa1 : RunCtx}  : ifast_spec_s.
Proof. exact ifast_s. Qed.

Section Local.
Context {RCa1 : RunCtx}.
Variable P : word -> Prop.
Variables M M' : mem.
Hypothesis AG : forall x, P x -> M' x = M x.

Lemma mem_is_local : forall a bs,
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> P x) ->
  0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  mem_is (run_segments R_segs rc_inp rc_sp rc_mb) M a bs -> mem_is (run_segments R_segs rc_inp rc_sp rc_mb) M' a bs.
Proof.
  intros a bs HP Ha Hn H. unfold mem_is in *.
  destruct bs as [|b bs']; [exact H|].
  assert (Ha' : bv_unsigned (w64 a) = a).
  { rewrite w64_unsigned, mod_small_u64; [reflexivity|]. cbn [length] in Hn. lia_std. }
  rewrite (rdn_ext (run_segments R_segs rc_inp rc_sp rc_mb) (length (b :: bs')) M' M (w64 a)); [exact H | |].
  - rewrite Ha'. rewrite <- two64_eq. exact Hn.
  - intros x Hx. apply AG. apply HP. rewrite Ha' in Hx. exact Hx.
Qed.

Lemma mem_u64_local : forall a v,
  (forall x : word, a <= bv_unsigned x < a + 8 -> P x) -> 0 <= a -> a + 8 <= two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' a v.
Proof.
  intros a v HP Ha Hn H. unfold mem_u64 in *.
  apply (mem_is_local a (Z_to_le_bytes 8 v)); rewrite ?length_Z_to_le_bytes; first [exact HP | exact Ha | exact Hn | exact H].
Qed.
Lemma mem_u32_local : forall a v,
  (forall x : word, a <= bv_unsigned x < a + 4 -> P x) -> 0 <= a -> a + 4 <= two64 ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' a v.
Proof.
  intros a v HP Ha Hn H. unfold mem_u32 in *.
  apply (mem_is_local a (Z_to_le_bytes 4 v)); rewrite ?length_Z_to_le_bytes; first [exact HP | exact Ha | exact Hn | exact H].
Qed.
Lemma mem_arr_local : forall k base n f,
  (forall x : word, base <= bv_unsigned x < base + k * n -> P x) ->
  mem_arr k (run_segments R_segs rc_inp rc_sp rc_mb) M base n f -> mem_arr k (run_segments R_segs rc_inp rc_sp rc_mb) M' base n f.
Proof.
  intros k base n f HP (A & B & C & D & H). split; [exact A | split; [exact B | split; [exact C | split; [exact D |]]]].
  intros i Hi. eapply mem_is_local; [ | nia | rewrite length_Z_to_le_bytes; nia | apply H; exact Hi].
  intros x Hx. apply HP. rewrite length_Z_to_le_bytes in Hx. nia.
Qed.

Lemma i_frame_local : forall cx,
  (forall x : word, c_u cx + - FR_INF <= bv_unsigned x < c_u cx -> P x) ->
  0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 ->
  i_frame cx M -> i_frame cx M'.
Proof.
  intros cx HP Hu1 Hu2 H. unfold i_frame in *. cbv zeta in H |- *.
  destr_conj H.
  repeat split; (eapply mem_u64_local; [ | | | eassumption]; [intros x Hx; apply HP; cbv [FR_INF]; lia_std | lia_std | lia_std]).
Qed.
Lemma i_hooks_local : forall cx,
  (forall x : word, c_u cx + 64 <= bv_unsigned x < c_u cx + 80 -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 ->
  i_hooks cx M -> i_hooks cx M'.
Proof.
  intros cx HP Hu1 Hu2 [A B].
  split; (eapply mem_u64_local; [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma i_cst_local : forall cx,
  (forall x : word, (c_u cx + 56 <= bv_unsigned x < c_u cx + 88) \/ (c_p cx <= bv_unsigned x < c_p cx + 7164) -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M -> i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M'.
Proof.
  intros cx HP Hu1 Hu2 Hp1 Hp2 H. unfold i_cst, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma st_at_local : forall cx st,
  (forall x : word, c_p cx + 8 <= bv_unsigned x < c_p cx + 168 -> P x) ->
  0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M'.
Proof.
  intros cx st HP Hp1 Hp2 H. unfold st_at, st_rest, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma strm_at_local : forall cx st,
  (forall x : word, (c_u cx <= bv_unsigned x < c_u cx + 36) \/ (c_p cx + 96 <= bv_unsigned x < c_p cx + 108) -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M'.
Proof.
  intros cx st HP Hu1 Hu2 Hp1 Hp2 H. unfold strm_at, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
End Local.

Definition cxw (u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra : Z) : ictx :=
  cxc u p q n 0 0 s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 ra.

(* THE FRAME DEFINITION IN THE LIST FORM: the slots are the layout's frame list, read from the stream's place;
   the definition binds two values for it: value 0 = the count of this pass, value 1 = the kept return value. *)
Definition tok_mem_l {RCa1 : RunCtx}  (cx : ictx) (st : ist) (rv : Z) (lf cf : Z -> Z) (M : mem) : Prop :=
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (run_segments R_segs rc_inp rc_sp rc_mb)
    (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv cx (Some st) [t_out st - (c_osz cx - t_cout st); rv]) M (c_u cx)
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zb_tok /\
  i_frame cx M /\ i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M /\ i_hooks cx M /\
  st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\ strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf.

Definition tok_pure (u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra s11v : Z) (st : ist) (lf cf : Z -> Z) : Prop :=
  (ra = RA_C1 \/ ra = RA_C2) /\ 0 <= cin0 <= n /\ 0 <= cout0 <= 262144 /\
  0 <= s5 < two64 /\ 0 <= s6 < two64 /\ 0 <= s7 < two64 /\ 0 <= s8 < two64 /\ 0 <= s9 < two64 /\ 0 <= s10 < two64 /\ 0 <= s11 < two64 /\
  0 <= s11v < two64 /\
  sinv (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st lf cf /\ cout0 < t_cout st /\ t_mode st <= DONE /\
  zc + FRA <= u /\ u + 208 <= 140737488355328 /\ 0 < p /\ p + STATE_SIZE <= zc.

(* THE VALUE LIST IN THE LIST FORM: the values of the layout's list, in the order of its rows. The definition
   binds for it: value 0 = the count of this pass, value 1 = the kept return value, and from value 2 on the
   values of the saved places that the place leaves free (a list: as many as the layout's list names). *)
Definition tok_regs_l (cx : ictx) (st : ist) (rv : Z) (fv : list Z) : list Z :=
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rvals (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv cx (Some st) ((t_out st - (c_osz cx - t_cout st)) :: rv :: fv))
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zb_tok.

(* THE INVARIANT IN THE LIST FORM: the value list and the frame definition in their list forms; the free values
   are a list; the one value that the pure part bounds is the value list's entry at the kit's fixed position
   (counted from 0) of its saved place *)
Definition zwtok_S9_l {RCa1 : RunCtx}  : ZWINV := fun u p q n zc sE sW M =>
  exists (s5 s6 s7 s8 s9 s10 s11 cin0 cout0 W0 ra rv : Z) (fv : list Z) (st : ist) (lf cf : Z -> Z),
    sE = [s5; s6; s7; s8; s9; s10; s11] /\
    sW = tok_regs_l (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st rv fv /\
    tok_pure u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra
      (nth 10 (tok_regs_l (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st rv fv) 0) st lf cf /\
    tok_mem_l (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st rv lf cf M.

(* THE LOCALITY THEOREM FOR THE LIST-FORM INVARIANT: the frame list is opened without a count *)
Theorem zw_local_l {RCa1 : RunCtx}  : zw_local_stmt_S9 zwtok_S9_l.
Proof.
  intros u p q n zc sE sW M M' AG H.
  destruct H as (s5 & s6 & s7 & s8 & s9 & s10 & s11 & cin0 & cout0 & W0 & ra & rv & fv & st & lf & cf & EsE & EsW & PURE & TM).
  exists s5, s6, s7, s8, s9, s10, s11, cin0, cout0, W0, ra, rv, fv, st, lf, cf.
  split; [exact EsE | split; [exact EsW | split; [exact PURE |]]].
  pose proof two64_eq as TW64.
  assert (HL : zc + FRA <= u /\ u + 208 <= 140737488355328 /\ 0 < p /\ p + STATE_SIZE <= zc).
  { unfold tok_pure in PURE. destr_conj PURE. split_conj; assumption. }
  clear PURE EsE EsW. cbv [FRA STATE_SIZE] in HL. dand HL as (Hu0 & Hu1 & Hp0 & Hp1).
  unfold tok_mem_l, cxw, cxc in *. icx_cbn.
  dand TM as (TMF & FRM & CST & HK & SAT & STRM & Hlens & Hcodes).
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zb_tok OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_RET] in TMF |- *.
  icx_cbn. destr_conj TMF.
  unfold in_fpw_S9, S9_ZWD, S9_INFL_N, S9_BUF, S9_BUF_N in AG.
  split_conj.
  all: first [ eapply (mem_u64_local _ M M' AG); [ | | | eassumption]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_frame_local _ M M' AG); [ | | | eassumption]; icx_cbn; cbv [FR_INF]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_hooks_local _ M M' AG); [ | | | eassumption]; icx_cbn; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_cst_local _ M M' AG); [ | | | | | eassumption]; icx_cbn; cbv [STATE_SIZE]; [intros x Hx; lia_std | lia_std | lia_std | lia_std | lia_std]
             | eapply (st_at_local _ M M' AG); [ | | | eassumption]; icx_cbn; cbv [STATE_SIZE]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (strm_at_local _ M M' AG); [ | | | | | eassumption]; icx_cbn; cbv [STATE_SIZE BUF]; [intros x Hx; lia_std | lia_std | lia_std | lia_std | lia_std]
             | eapply (mem_arr_local _ M M' AG); [ | eassumption]; cbv [N_LENS N_CODES]; intros x Hx; lia_std
             ].
Qed.
End S_Tok.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_Entry. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_Ret. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import S_Entry. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.S_Uw. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_LeaveA. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_Leave. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_Inflate. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.S_U2A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2B. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2C. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import S_ZA. Import S_Tok.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Lemma sinv_rewin : forall u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 ra st lf cf wh wn,
  sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 ra) st lf cf ->
  w <> 0 -> 0 <= wh -> wh <= WIN_SIZE -> 0 <= wn -> wn < WIN_SIZE -> (wh < WIN_SIZE -> wn = wh) ->
  sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 ra) (set_win st wh wn) lf cf.
Proof.
  intros u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 ra st lf cf wh wn (RG & W & P & Mo) Hw H1 H2 H3 H4 H5.
  destruct st; unfold sinv, set_win, RNG, WIN, PROG, MODE, Wm, tables_live, ctable_live, cxc in *; cbn -[Z.add Z.mul Z.sub Z.pow] in *.
  split; [| split; [| split; [exact P | exact Mo]]].
  - destr_conj RG. split_conj; try assumption; lia_std.
  - split; [intros E; exfalso; exact (Hw E) | intros _; split_conj; assumption].
Qed.

Lemma wok0 : forall p q n zc, DATA_LO + DATA_LEN <= zc -> wok p q n zc 0.
Proof.
  intros p q n zc Hz. unfold wok, ZSEP. cbv [WIN_SIZE]. cbv [DATA_LO DATA_LEN] in Hz.
  split_conj; try lia_std; try (left; reflexivity). reflexivity.
Qed.

Section ZB.
Context {RCa1 : RunCtx}.
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet).
Variable zc : Z.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < n -> 0 <= fin i < 256.
Hypothesis Hu0 : zc + FRA <= u. Hypothesis Hzimg : DATA_LO + DATA_LEN <= zc. Hypothesis Hu1 : u + 208 <= 140737488355328. Hypothesis Hua : u mod 16 = 0.
Hypothesis Hp0 : 0 < p. Hypothesis Hp1 : p + STATE_SIZE <= zc. Hypothesis Hpa : p mod 16 = 0.
Hypothesis Hq1 : 1 <= q. Hypothesis Hn0 : 0 <= n. Hypothesis Hn1 : n < 67108864. Hypothesis Hqn : q + n <= zc.
Hypothesis Spq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p).
Hypothesis Spob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p).
Hypothesis Sobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF).
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p).
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.
Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.
Variable w : Z.
Hypothesis Hw : wok p q n zc w.
Variables (site : bool) (cin0 cout0 W0 rv : Z) (st : ist) (lf cf : Z -> Z).
Hypothesis Hcin0 : 0 <= cin0 <= n.
Hypothesis Hcout0 : 0 <= cout0 <= 262144.
Hypothesis SI : sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) st lf cf.
Hypothesis Hcc : cout0 < t_cout st.

Local Ltac open_zb :=
  zkeysb; unfold L_UW_RET, L_RET, L_ZB, T_ZE1, T_ZE2, RA2 in *;
  cbv [STATE_SIZE FRA WIN_SIZE ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *;
  pose proof two64_eq as TW64.

(* a memory fact of the goal's form, at a place that is equal by arithmetic to the place of a fact in hand *)
Local Ltac mem_u64_at :=
  lazymatch goal with
  | |- mem_u64 ?SG ?MM ?AA _ =>
      match goal with
      | HH : mem_u64 SG MM ?BB _ |- _ => replace AA with BB by lia_std; exact HH
      end
  end.

(* a memory fact of the goal's form, found among the slots of the frame list in hand *)
Local Ltac mem_u64_fr :=
  lazymatch goal with
  | HF : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds _ _ _ _ _ |- _ =>
      let HG := fresh "HG" in
      pose proof HF as HG;
      cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
           OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth
           OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zb_tok OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_RET] in HG;
      icx_cbn; destr_conj HG; mem_u64_at
  end.

(* OPENERS OF THE LIST FORM (they only unfold, split and name): every list-form hypothesis: the meaning over
   the layout's list is unfolded, the conjunction split and its parts named; the same for a goal *)
Local Ltac open_lists :=
  repeat match goal with
         | HH : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zb_v cxc Kra] in HH;
             icx_cbn; zkeysb; cbn [Pos.eqb] in HH; destr_conj HH
         end.
Local Ltac split_lists :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zb_v];
  split_conj.

(* THE WALK STATEMENT IN THE LIST FORM. The place's facts are ONE list of the layout, taken at the model
   state `st`, and the frame definition's list form. The statement binds three values for the list:
   value 0 = the count of this pass, value 1 = the kept return value, value 2 = the window's place. *)
Theorem zb_cps_l : forall Rb l M,
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
    (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) (Some st)
       [t_out st - (262144 - t_cout st); rv; w])
    Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zb_v ->
  rom_ok M -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  (w <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M w WIN_SIZE) ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  tok_mem_l (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) st rv lf cf M ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M w ->
  KZE1 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M w ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZB (zupd Rb l) M MD) T.
Proof.
  intros Rb l M RH ROM Wstk Wp Ww Hin TM HZE2 HZE1.
  open_lists.
  pose proof Hw as Hw'. dand Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn.
  assert (RF : 0 <= cin /\ cin <= n /\ 0 <= cout /\ cout <= 262144 /\ 262144 - cout <= out /\ out <= 262144 /\ out - (262144 - cout) <= cout).
  { clear -RNG_. unfold RNG, cxc in RNG_. icx_cbn. destr_conj RNG_. split_conj; assumption. }
  clear RNG_. dand RF as (Rci0 & Rci1 & Rco0 & Rco1 & Rou0 & Rou1 & Rou2).
  unfold tok_mem_l in TM. dand TM as (TMF & FRM & CST & HK & SAT & STRM & Hlens & Hcodes).
  unfold cxc in *. icx_cbn.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. unfold wsz in CST'. icx_cbn. cbn [Z.eqb] in CST'.
  dand CST' as (C64 & C88 & Cp0 & Cp16 & Cp48 & Cp56 & Cp60 & Cp72 & Cp7144).
  dand (out_arr_exists M) as (fo & HOB & Hfo). cbv [BUF_N] in HOB.
  open_zb.
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZB].
  (* the callee's resume: its frame stands below the walk's own frame; the walk's frame size and the output
     buffer are taken BY NAME; the place it returns to and the values its frame keeps are found by the
     frame facts in hand *)
  let fr := eval cbv in (- FR_INF) in
  let ob := eval cbv in BUF in
  eapply (uw_resume_s MEMCPY Rb l M MD T p ob 262144 w cout (out - (262144 - cout)) (u + fr) _
            _ _ _ _ _ zc fo Hh).
  all: lazymatch goal with
       | |- forall R' M', w = 0 -> _ => idtac
       | |- forall R' M' whave' wnext', _ => idtac
       | |- ZSEP _ => first [ assumption | unfold ZSEP; lia_std ]
       | |- mem_u64 _ _ _ _ => first [ assumption | mem_u64_fr ]
       | |- mem_u32 _ _ _ _ => assumption
       | |- mem_arr _ _ _ _ _ _ => exact HOB
       | |- mem_wr _ _ _ _ => first [ assumption | eapply mem_wr_sub; [exact Wstk | lia_std | lia_std] ]
       | |- _ -> mem_wr _ _ _ _ => exact Ww
       | |- forall i, _ -> _ => intros i _; apply Hfo
       | |- _ => first [ zreg | assumption | reflexivity | lia_std ]
       end.
  -
    intros R' M' Wz. intros. zimps. zkeys.
    clear SAT STRM Hlens Hcodes HOB Hfo CST Cp60 Cp72 TMF.
    pose proof (ctx_ok_cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Spob Sobq Sprom
                  Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 0 cin0 cout0 W0 (ra_site site) (wok0 p q n zc Hzimg) Hcin0 Hcout0
                  ltac:(destruct site; [left | right]; reflexivity)) as CX0.
    pose proof CX0 as CXo. unfold cxc in CXo. dand CXo as (_ & _ & SEP).
    match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' _ |- _ =>
      pose proof HP as HPw; zreattachL HP end.
    clear SEP.
    let ob := eval cbv in BUF in
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(u + -1024, 1024); (u, 112); (p, 7176); (ob, 262144)] ltac:(ranges_ok_tac)) as HST.
    let ob := eval cbv in BUF in
    assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(u + -1024, 1024); (u, 112); (p, 7176); (ob, 262144)]) M').
    { eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M _) HPw).
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; ranges_within_tac. }
    clear HPw.
    pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
    cbv zeta in FRM'. destr_conj FRM'.
    rewrite Wz in *.
    (* ONE RUN from the callee's return place to the walk's return place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (ret_s _ R9 [] Mx MD T (-4) CX0 Hh) end).
    + unfold s_regs_ret, cxc, Kra; icx_cbn; zkeys; cbn [Pos.eqb]; split_conj; zreg.
    + exact FRM.
    + intros R9 HB.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        eapply (u2_krx u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hp0 Hp1 0 (wok0 p q n zc Hzimg) HZE2 HZE1
                  site cin0 cout0 W0 M (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_u2 u p 0)) R9 Mx (-4) 16210) end.
      * cbv. discriminate.
      * exact HB.
      * unfold s_std, i_cst, wsz, cxc; icx_cbn; cbn [Z.eqb]; cbv [BUF BUF_N]; split_conj; try assumption.
        all: first [ apply buf_writable | intros i Hi; exfalso; lia_std ].
      * unfold cxc; icx_cbn. assumption.
      * unfold reach; cbv [HEAD DICTID MEM]; lia_std.
      * unfold fp_call, fp_loop, wsz, cxc; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE BUF]; cbn [Z.eqb app].
        eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M _) HAG).
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; ranges_within_tac.
  -
    intros R' M' whave' wnext' Wnz. intros. zimps. zkeys.
    specialize (Ww Wnz).
    pose proof SAT as SAT'. destruct SAT' as [Hmode SREST']. unfold st_rest, cxc in SREST'. icx_cbn. destr_conj SREST'. clear SAT.
    unfold cxc in Hmode; icx_cbn.
    clear Cp60 Cp72 CST HOB Hfo TMF.
    repeat match goal with
           | H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) _ |- _ => clear H
           | H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) _ |- _ => clear H
           end.
    pose proof (ctx_ok_cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Spob Sobq Sprom
                  Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 w cin0 cout0 W0 (ra_site site) Hw Hcin0 Hcout0
                  ltac:(destruct site; [left | right]; reflexivity)) as CX1.
    pose proof CX1 as CXo. unfold cxc in CXo. dand CXo as (_ & _ & SEP).
    lazymatch goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' ?rs |- _ =>
      pose proof HP as HPw; unfold uw_res_fp in HP; cbv [WIN_SIZE] in HP;
      lazymatch type of HP with mpostL _ _ _ ?rs' =>
        apply (mem_arr_magreeL (run_segments R_segs rc_inp rc_sp rc_mb) 1 M M' rs' q n fin (proj1 HP)) in Hin;
        [| pose proof Spq as D1; pose proof W5 as D2; unfold ZSEP in D1, D2; clear SEP;
           zconj_norm; repeat split; first [ exact I | lia_std ] ]
      end;
      zreattachL HP end.
    clear SEP.
    assert (HZW : KZW u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc w) by (unfold KZW; intros; exfalso; lia_std).
    assert (OBLOW1 : c_ob (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 (ra_site site))
                     + c_osz (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 (ra_site site))
                     <= c_u (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 (ra_site site)) - FRA).
    { unfold cxc; icx_cbn; cbv [BUF FRA]; lia_std. }
    pose proof (pcall_all u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hfin Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn
                  Spq Spob Sobq Sprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 MEMCPY ADLER
                  A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
                  A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH w Hw HZE2 HZE1 HZW) as PC.
    pose proof (u2_krl u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hp0 Hp1 Hn1 Hqn Spq Spob Sobq w Hw HZE2 HZE1
                  _ (PC _) site cin0 cout0 W0 M Hcin0 Hcout0 (Z.le_refl _) (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_u2 u p w))) as HKRL.
    pose proof (u2_krx u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hp0 Hp1 w Hw HZE2 HZE1
                  site cin0 cout0 W0 M (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_u2 u p w))) as HKRX.
    (* the leave statement is applied BY THE NAMES of its parts; what it asks besides is closed by form *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply leave_uwret_s with
        (cx := cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 (ra_site site))
        (fin := fin) (M0 := M) (Rb := R9) (l := []) (M := Mx)
        (st :=
                (set_win (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) whave' wnext')
        ) (rv := rv) (uwret := 0) (lf := lf) (cf := cf) end.
    all: first [ exact CX1 | exact Hh | exact OBLOW1 | exact HKRL | exact HKRX
               | eapply sinv_rewin; [exact SI | exact Wnz | assumption ..]
               | unfold cxc; icx_cbn; zreg
               | unfold set_win, cxc; icx_cbn; zreg
               | left; reflexivity
               | unfold s_std, i_cst, wsz, cxc; icx_cbn; rewrite (proj2 (Z.eqb_neq w 0) Wnz); cbv [BUF BUF_N WIN_SIZE]; split_conj;
                 first [ assumption | apply buf_writable ]
               | unfold st_at, st_rest, set_win, cxc; icx_cbn; split_conj; assumption
               | unfold strm_at, set_win, cxc; icx_cbn; unfold strm_at, cxc in STRM; icx_cbn; exact STRM
               | assumption
               | unfold fp_call, fp_loop, wsz, cxc; icx_cbn; rewrite (proj2 (Z.eqb_neq w 0) Wnz); cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE BUF]; cbn [app];
                 eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M _) HPw);
                 intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold uw_res_fp; cbv [WIN_SIZE]; ranges_within_tac ].
Qed.
End ZB.
