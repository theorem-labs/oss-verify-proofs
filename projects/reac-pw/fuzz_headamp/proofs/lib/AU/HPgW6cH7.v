(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the head of ent_build's case 7 (pod.h:352-354)
   inside LLVMFuzzerTestOneInput (0x80c40), from the case entry 0x81d88 to the take block 0x8244c,
   HPgW6cCase.w6c_head7_stmt. Proves no function (kind: segment lemma).

   THE CODE (registers as in HPgW6cCase.w6c_in: s1 = R, s11 = SHADOW_OFF, s2 = cur, a7 = cur - 1, t1 = |r| + 1,
   s4 = |r|, a6 = 1):
     0x81d88  beqz s4 -> 0x820e4                      nothing is left
     0x820e4  a1 := 0; a2 := 0; s4 := [R+0x130] (= F + 0x210); s7 := [R+0x148] (= pp); j 0x8244c
     0x81d8c  a0 := s2 + 1; bltu a6,a0 -> 0x81d98      the UBSan pointer test (its trap arm 0x81d94 needs
                                                     cur + 1 <=u 1, which 2 <= cur rules out)
     0x81d98  the instrumented check of s2 (slow block 0x82810); s4 := [R+0x130]; s7 := [R+0x148]
     0x81db0  a1 := t = [s2]; s2 := a7 + 2; a1 := t mod 21 (the multiply by 0x87, 0x81db8 .. 0x81de8)
     0x81dec  sw a1,0(s4)                             e62.type := t mod 21
     0x81df0  a1 := 2; bne t1,a1 -> 0x82408
     0x81df8  (|r| = 1) a1 := 0; a2 := 0; j 0x8244c
     0x82408  (|r| >= 2) a1 := s2 + 1; bltu a6,a1 -> 0x82414 (trap arm 0x82410 as above); the check of s2 (slow
              block 0x82874); a2 := s = [s2]; a1 := t1 - 3 (= |r| - 2); s2 := a7 + 3; a0 := [R+0x10] (= 0x15555556);
              a2 := s - 12 * ((s * 0x15555556) >> 32) (= s mod 12)                          -> 0x8244c
   Registers and cells used: x9 = s1, x27 = s11, x18 = s2, x17 = a7, x6 = t1, x20 = s4, x16 = a6, x10 .. x13,
   x23 = s7; R+0x10, R+0x130, R+0x148 (read); e62.type [F+0x210, F+0x214) (written).
   THE PROOF: the input split by its length (0, 1, at least 2); the entry state HPgW6cCase.w6c_head_entry with that
   many input bytes in its region, the exact bound of what is left (atom 20: 0 .. 0, 1 .. 1, 2 .. 2^47) and the
   kind byte's address bounded by 2^47, 2^47 - 3, 2^47 - 4 (so that each input byte's shadow cell lies in the
   shadow span). The engine decides the two UBSan tests from the cursor's bound and, for |r| >= 2, both length
   tests; the tests it cannot decide (beqz s4 at |r| = 0, bne t1,a1 at |r| = 1) are split by srr_branch_tok, the
   other arm closed by the atom's value. One token-engine run per arm segment, each input read's obligation paid
   from w6c_in's range_addressable over the input; the post read off the last state (HPgW6cEng.w6c_post_of_run),
   t mod 21 and s mod 12 by the 256-value check HPgW6cEng.w6c_by256. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSteps HPgCaseBJ
  HPgW6cEng HPgW6cFill HPgW6cTake HPgW6cCase HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the model of case 7: the type t mod 21, the size s mod 12, what is left after t and s *)
Lemma w6c7_tk : forall r, w6c_tk_model 7 r (u32_b r 0 mod 21) (u32_b r 1 mod 12) (skipn 2 r).
Proof.
intros r. pose proof (Z.mod_pos_bound (u32_b r 0) 21 ltac:(lia)) as H0.
pose proof (Z.mod_pos_bound (u32_b r 1) 12 ltac:(lia)) as H1.
split; [lia|]. split; [lia|]. split; [exists 2%nat; reflexivity|].
rewrite w6c7_model. destruct r as [|b0 [|b1 r']]; reflexivity.
Qed.

(* the write windows of a head state (any state with the skeleton of w6c_regs m): e62.type *)
Lemma w6c7_wr : forall E rs m a, YP09.skeleton rs = YP09.skeleton (w6c_regs m) -> in_wrange E rs a ->
  bv_unsigned (ew E 32) + 0x210 <= a < bv_unsigned (ew E 32) + 0x214.
Proof.
intros E rs m a Hsk Ha. apply (in_wrange_skeleton E rs (w6c_regs m) a Hsk) in Ha. destruct Ha as (r & Hin & Ha).
destruct m as [|m]; unfold w6c_regs in Hin; cbn [In] in Hin;
  repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val w6c_RS w6c_RE w6c_RI] in Ha; lia.
Qed.
Lemma w6c7_wrH : forall E rs m F a, YP09.skeleton rs = YP09.skeleton (w6c_regs m) -> bv_unsigned (ew E 32) = F ->
  in_wrange E rs a -> w6c_wrH F a.
Proof. intros E rs m F a Hsk U Ha. pose proof (w6c7_wr E rs m a Hsk Ha) as X. rewrite U in X. unfold w6c_wrH. lia. Qed.
Lemma w6c7_awr : forall E rs m STK sp0 FP bl0 blc lyc own F pos,
  YP09.skeleton rs = YP09.skeleton (w6c_regs m) -> bv_unsigned (ew E 32) = F -> In (4, pos) own ->
  F = frame_addr lyc 4 pos -> awr_ok E rs STK sp0 FP bl0 blc lyc own.
Proof.
intros E rs m STK sp0 FP bl0 blc lyc own F pos Hsk U32 Hown HF a Ha. pose proof (w6c7_wr E rs m a Hsk Ha) as Hw.
rewrite U32 in Hw. unfold awr_byte. right; right; right. exists 4, pos. split; [exact Hown|]. left.
unfold in_zr. cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
Qed.
(* e62.type of a final state, from region 1's chunk at 0x210 *)
Lemma w6c7_ty : forall E m F lo hi wlo whi cs e ty,
  region_ok rsegs E m (YP09.mkRegion (Some 32%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 32) = F ->
  In (YP09.mkChunk 0x210 (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 ty -> 0 <= ty < 2 ^ 32 ->
  val_mem rsegs m (F + 0x210) 4 ty.
Proof.
intros E m F lo hi wlo whi cs e ty Hr U Hin He Hty.
exact (w6c_field E m 32%nat F cs lo hi wlo whi 0x210 4%N e ty Hr U Hin He
  ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)).
Qed.

(* the obligation of an input read at cur - 1 + j: the byte is addressable *)
Local Ltac w6c7_obl Hrar E27 E17 :=
  unfold w6c_Bx; eapply (obl_of_range rsegs _ _ _ _ _ _ _ _ Hrar);
  [ apply (U_atom _ 27 SHADOW_OFF E27); unfold SHADOW_OFF; lia
  | rewrite (U_atom_off _ 17 _ _ E17) by lia; lia
  | rewrite (U_atom_off _ 17 _ _ E17) by lia; cbn [length]; lia ].
(* the write windows of a run from a head state lie in e62.type *)
Local Ltac w6c7_wrl m U :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; refine (w6c7_wrH _ _ m _ a _ U Ha); vm_compute; reflexivity.
Local Ltac w6c7_awr_tac m U F pos Hown HF :=
  eapply (w6c7_awr _ _ m _ _ _ _ _ _ _ F pos); [vm_compute; reflexivity | exact U | exact Hown | exact HF].
(* the type and size goals sv_denot E e = Z_to_bv 64 (v mod d), v = u32_b rr i, e reading atom n only
   (En : ew E n = Z_to_bv 64 v) *)
Local Ltac w6c7_mod En rr i d :=
  unfold w64; change (Z_to_bv 64 (u32_b rr i mod d)) with (Z_to_bv 64 ((fun x => x mod d) (u32_b rr i)));
  let Hv := constr:(u32_b_range rr i) in w6c_by256 En Hv.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the leaf at 0x8244c: the post from the last state of the arm's runs *)
Local Ltac w6c7_leaf B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc F HAE KE Hpres :=
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msf), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msf) _ _ |- _ =>
    let Kept := fresh "Kept" in
    assert (Kept : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w6c_clob -> getr (ms_regs msf) r = getr regs r)
      by (eapply (regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HSx); [env_agree_chain HAE | vm_compute; reflexivity]);
    apply (w6c_post_of_run B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_T7 w6c_clob
      (w6c_wrH F) _ _ _ msf _ HSx eq_refl eq_refl HJx);
    [ cb_kio | exact Kept | exact KE | unfold w6c_hpostT; split; [reflexivity|] ]
  end.

Theorem w6c_head7 : w6c_head7_stmt B MT.
Proof using MTL.
unfold w6c_head7_stmt, w6c_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp r Hctx Hin.
pose proof Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & V10 & V118 & V130 & V138 & V148
  & Hpp1 & Hpp2 & Hez & HraE & HhE & Hr & Hrar & Hhr & Hamr & Hc2 & Hdis & Ht6 & Ht8 & Hrom).
pose proof Hctx as (HJ & HR32 & HRc & HRsp & Hsp47 & HSTK & Hown & HF & HF1 & HF2 & HF32 & HFapp & HFp).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof asan_consts as (Hceil & _).
assert (HFb : 4096 <= F <= 2 ^ 47 - 1024) by lia.
assert (Hcr : cur + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (Hpp : 0 <= pp <= 2 ^ 47) by (unfold Layout.PP_SIZE in Hpp2; lia).
pose proof (w6c7_tk r) as HM. pose proof HM as (Hsz & Hty & _).
unfold cfg_at. change (w6c_pc 7) with W6C_D7. change (w64 W6C_D7) with (Z_to_bv 64 W6C_D7).
destruct r as [|b0 [|b1 r']]; cycle 1.
- (* ======================= one byte is left: 0x81d88 .. 0x81df4, then 0x81df8 .. 0x8244c ======================= *)
  destruct (w6c_head_entry B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp [b0]
    W6C_D7 1 1 1 (2 ^ 47 - 3) Hctx Hin ltac:(unfold W6C_D7; lia) ltac:(cbn [length] in Hcr; lia) ltac:(cbn; lia)
    ltac:(cbn; lia) ltac:(lia)) as [HS SHOK].
  remember (Ereg regs (w6c_extra F (u32_b [b0] 0) (u32_b [b0] 1) pp)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (w6c_extra F (u32_b [b0] 0) (u32_b [b0] 1) pp)) E)
    by (subst E; apply env_agree_refl).
  assert (E17 : ew E 17 = Z_to_bv 64 (cur - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E20 : ew E 20 = Z_to_bv 64 1) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (w6c_e32 regs F _ _ pp)).
  assert (E33 : ew E 33 = Z_to_bv 64 (u32_b [b0] 0)) by (subst E; exact (w6c_e33 regs F _ _ pp)).
  assert (E35 : ew E 35 = Z_to_bv 64 pp) by (subst E; exact (w6c_e35 regs F _ _ pp)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  clear HE.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_T7.
  { w6c7_obl Hrar E27 E17. }
  { w6c7_awr_tac 1%nat U32 F pos Hown HF. }
  w6c_ew HS E17. w6c_ew HS E20. w6c_ew HS E32. w6c_ew HS E33. w6c_ew HS E35. w6c_ew HS U32.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6c_wrH F a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { apply (cb_kept_run (w6c_wrH F) E _ (w_H W) memc memc (ms_mem ms) (fun _ _ _ => eq_refl) HFr).
    w6c7_wrl 1%nat U32. }
  clear HFr. rename HG into HG1.
  srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan.
  + (* t1 <> 2 is impossible here *)
    exfalso. revert Hc. rewrite (w6c_den_off _ 20 1 1 E20') by lia. rewrite w6c_den_lit by lia.
    vm_compute. intros X. discriminate X.
  + (* t1 = 2: 0x81df8 .. 0x8244c *)
    aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_T7.
    { w6c7_awr_tac 1%nat U32' F pos Hown HF. }
    w6c_keep (w6c_wrH F) ltac:(w6c7_wrl 1%nat U32').
    w6c_ew HS E17'. w6c_ew HS E32'. w6c_ew HS E33'. w6c_ew HS E35'. w6c_ew HS U32'.
    assert (Hpres : forall o, 0 <= o < 1024 -> apresent (w_H W) (ms_mem ms0) (F + o)).
    { intros o Ho. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact (HFp o Ho). }
    w6c_rnth HS 1%nat Hr1.
    w6c7_leaf B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc F HAE KE Hpres.
    exists (u32_b [b0] 0 mod 21), (u32_b [b0] 1 mod 12), (skipn 2 [b0]).
    split; [exact HM|].
    split; [w6c_reg HS (12%bv : bv 5); rewrite w6c_den_lit by lia; reflexivity|].
    split; [w6c_reg HS (11%bv : bv 5); rewrite w6c_den_lit by lia; reflexivity|].
    split; [w6c_reg HS (18%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 17 (cur - 1) 2 E17'') by lia;
            f_equal; cbn [length skipn]; lia|].
    split; [w6c_reg HS (20%bv : bv 5); unfold w64; apply w6c_den_off; [exact E32'' | lia | lia]|].
    split; [w6c_reg HS (23%bv : bv 5); unfold w64; apply w6c_den0; [exact E35'' | lia]|].
    split; [|exact Hpres].
    eapply (w6c7_ty _ _ F _ _ _ _ _ _ _ Hr1 U32'');
      [ cbn [In]; repeat (first [left; reflexivity | right]) | w6c7_mod E33'' [b0] 0%nat 21 | exact Hty ].
- (* ======================= at least two bytes are left: 0x81d88 .. 0x8244c ======================= *)
  destruct (w6c_head_entry B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp (b0 :: b1 :: r')
    W6C_D7 2 2 (2 ^ 47) (2 ^ 47 - 4) Hctx Hin ltac:(unfold W6C_D7; lia) ltac:(cbn [length] in Hcr; lia)
    ltac:(cbn [length] in Hcr |- *; lia) ltac:(cbn; lia) ltac:(lia)) as [HS SHOK].
  remember (Ereg regs (w6c_extra F (u32_b (b0 :: b1 :: r') 0) (u32_b (b0 :: b1 :: r') 1) pp)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (w6c_extra F (u32_b (b0 :: b1 :: r') 0) (u32_b (b0 :: b1 :: r') 1) pp)) E)
    by (subst E; apply env_agree_refl).
  assert (E17 : ew E 17 = Z_to_bv 64 (cur - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E20 : ew E 20 = Z_to_bv 64 (Z.of_nat (length (b0 :: b1 :: r'))))
    by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (w6c_e32 regs F _ _ pp)).
  assert (E33 : ew E 33 = Z_to_bv 64 (u32_b (b0 :: b1 :: r') 0)) by (subst E; exact (w6c_e33 regs F _ _ pp)).
  assert (E34 : ew E 34 = Z_to_bv 64 (u32_b (b0 :: b1 :: r') 1)) by (subst E; exact (w6c_e34 regs F _ _ pp)).
  assert (E35 : ew E 35 = Z_to_bv 64 pp) by (subst E; exact (w6c_e35 regs F _ _ pp)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  clear HE.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_T7.
  { w6c7_obl Hrar E27 E17. }
  { w6c7_obl Hrar E27 E17. }
  { w6c7_awr_tac 2%nat U32 F pos Hown HF. }
  w6c_ew HS E17. w6c_ew HS E20. w6c_ew HS E32. w6c_ew HS E33. w6c_ew HS E34. w6c_ew HS E35. w6c_ew HS U32.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6c_wrH F a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { apply (cb_kept_run (w6c_wrH F) E _ (w_H W) memc memc (ms_mem ms) (fun _ _ _ => eq_refl) HFr).
    w6c7_wrl 2%nat U32. }
  assert (Hpres : forall o, 0 <= o < 1024 -> apresent (w_H W) (ms_mem ms) (F + o)).
  { intros o Ho. apply (apresent_grows _ _ _ _ HG). exact (HFp o Ho). }
  w6c_rnth HS 1%nat Hr1.
  w6c7_leaf B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc F HAE KE Hpres.
  exists (u32_b (b0 :: b1 :: r') 0 mod 21), (u32_b (b0 :: b1 :: r') 1 mod 12), (skipn 2 (b0 :: b1 :: r')).
  split; [exact HM|].
  split; [w6c_reg HS (12%bv : bv 5); w6c7_mod E34' (b0 :: b1 :: r') 1%nat 12|].
  split; [w6c_reg HS (11%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 20 _ (-2) E20') by (cbn [length] in *; lia);
          f_equal; change (skipn 2 (b0 :: b1 :: r')) with r'; cbn [length]; lia|].
  split; [w6c_reg HS (18%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 17 (cur - 1) 3 E17') by lia;
          f_equal; change (skipn 2 (b0 :: b1 :: r')) with r'; cbn [length]; lia|].
  split; [w6c_reg HS (20%bv : bv 5); unfold w64; apply w6c_den_off; [exact E32' | lia | lia]|].
  split; [w6c_reg HS (23%bv : bv 5); unfold w64; apply w6c_den0; [exact E35' | lia]|].
  split; [|exact Hpres].
  eapply (w6c7_ty _ _ F _ _ _ _ _ _ _ Hr1 U32');
    [ cbn [In]; repeat (first [left; reflexivity | right]) | w6c7_mod E33' (b0 :: b1 :: r') 0%nat 21 | exact Hty ].
- (* ======================= nothing is left: 0x81d88 -> 0x820e4 .. 0x8244c ======================= *)
  destruct (w6c_head_entry B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp []
    W6C_D7 0 0 0 (2 ^ 47) Hctx Hin ltac:(unfold W6C_D7; lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
    ltac:(lia)) as [HS SHOK].
  remember (Ereg regs (w6c_extra F (u32_b [] 0) (u32_b [] 1) pp)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (w6c_extra F (u32_b [] 0) (u32_b [] 1) pp)) E)
    by (subst E; apply env_agree_refl).
  assert (E17 : ew E 17 = Z_to_bv 64 (cur - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E20 : ew E 20 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (w6c_e32 regs F _ _ pp)).
  assert (E35 : ew E 35 = Z_to_bv 64 pp) by (subst E; exact (w6c_e35 regs F _ _ pp)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  clear HE.
  srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan.
  + (* s4 = 0: 0x820e4 .. 0x8244c *)
    aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_T7.
    { w6c7_awr_tac 0%nat U32 F pos Hown HF. }
    w6c_ew HS E17. w6c_ew HS E32. w6c_ew HS E35. w6c_ew HS U32.
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6c_wrH F a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
    { apply (cb_kept_run (w6c_wrH F) E _ (w_H W) memc memc (ms_mem ms) (fun _ _ _ => eq_refl) HFr).
      w6c7_wrl 0%nat U32. }
    assert (Hpres : forall o, 0 <= o < 1024 -> apresent (w_H W) (ms_mem ms) (F + o)).
    { intros o Ho. apply (apresent_grows _ _ _ _ HG). exact (HFp o Ho). }
    w6c_rnth HS 1%nat Hr1.
    w6c7_leaf B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc F HAE KE Hpres.
    exists (u32_b [] 0 mod 21), (u32_b [] 1 mod 12), (skipn 2 []).
    split; [exact HM|].
    split; [w6c_reg HS (12%bv : bv 5); rewrite w6c_den_lit by lia; reflexivity|].
    split; [w6c_reg HS (11%bv : bv 5); rewrite w6c_den_lit by lia; reflexivity|].
    split; [w6c_reg HS (18%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 17 (cur - 1) 1 E17') by lia;
            f_equal; cbn [length skipn]; lia|].
    split; [w6c_reg HS (20%bv : bv 5); unfold w64; apply w6c_den_off; [exact E32' | lia | lia]|].
    split; [w6c_reg HS (23%bv : bv 5); unfold w64; apply w6c_den0; [exact E35' | lia]|].
    split; [|exact Hpres].
    eapply (w6c7_ty _ _ F _ _ _ _ _ _ _ Hr1 U32');
      [ cbn [In]; repeat (first [left; reflexivity | right]) | rewrite w6c_den_lit by lia; reflexivity | exact Hty ].
  + (* s4 <> 0 is impossible here *)
    exfalso.
    assert (Ht : (bv_unsigned (sv_denot E (SOff 20 0)) =? bv_unsigned (sv_denot E (SLit 0))) = false) by exact Hc.
    cbn [sv_denot] in Ht. rewrite E20 in Ht. discriminate Ht.
Qed.
End d.
End b.

Print Assumptions w6c_head7.
