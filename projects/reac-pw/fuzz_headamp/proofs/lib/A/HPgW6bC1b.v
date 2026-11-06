(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC1b.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths renamed, every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0), the real-frame cells by the plan's slot map (s5's R+0x70 -> R+0x98, pp R+0x80 -> R+0xf0, vb R+0xb0 -> R+0xd0, &e.body R+0xc0 -> R+0xe0, the cursor's spill R+0xc8 -> R+0x68, &e R+0xf0 -> R+0x110) with the read-only R-based region re-cut to [R+0x68, R+0x118) (chunks in address order), the frame for locals of class 4 (1024 bytes), the real frame of 0x1e0 bytes, RPgCfgChanges' lemmas -> HPgSteps' and HPgW7bBase.kept_run. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the tail of case 1 of
   ent_build's `switch (kind % 10)` (pod.h:213-217, 290-294) inside LLVMFuzzerTestOneInput (0x80bc0), from the
   return of __asan_memcpy (0x81fec) to the join J 0x8237c. Proves no function (kind: segment lemma).

   THE CODE (s5 = s9 = len, s8 = F + 0xf8 = &e.body, s4 = the kind byte sign-extended):
     0x81fec  a0 := s5 + 1; sb zero,len(s8) (the NUL, no instrumented check); a2 := [R+0x110] (= &e);
              sw 8,0(a2) (e.type = POD_STRING); sw a0,4(a2) (e.size = len + 1); bgez s4 -> 0x82250
     0x82250  s11 := [R+0xf0]; 0x82254 s4 := [R+0xd0]; s9 := [R+0x68]; j 0x81b80: s5 := [R+0x98]; j J
     0x8200c  (kind & 0x80) s11 := [R+0xf0]; bltu 0x5d,s9 (not taken: len <= 18); a0 := e.body + len + 1;
              the instrumented check of a0 (slow block 0x8275c) with `ld s4,0xd0(s1)`; sb 'x'; a0 := e.body + len + 2;
              the check of a0 (slow block 0x82768) with `ld s9,0x68(s1)`; sb zero; e.size := len + 3;
              j 0x81b80 (then as above)
   THE ENTRY STATE, over Ereg regs [F; vb; cur; pp + 0x4000; pp] (atoms 32 .. 36):
     c1_rTR  based at s1 = R: the read-only cells [R+0x68] .. [R+0x110].
     c1_rE1  based at F: e.type, e.size [F+0xf0, F+0xf8), written.
     c1_rE2  based at F: e.body[len .. len + 3), written, 0 at the entry (memcpy wrote e.body[0 .. len) only).
     s5, s9 pinned to the literal len, s8 to F + 0xf8. The shadow entry over e (atom 32, [0xf0, 0x158)) covers both
     checked stores, so the token engine asks no obligation: e is in scope (its 104 bytes are addressable).
   The branch on s4 is split by srr_branch_tok; len takes the five lengths of the vocab strings (12, 13, 14, 15, 18),
   each a closed numeral in the state. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgSteps HPgW6aBase HPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgEntBKit HPgW7bBase HPgW6aTail HPgW6aC2h HPgW6bC1a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the entry state ======================================== *)
Definition c1_rTR : YP09.region := YP09.mkRegion (Some 9%nat) 0x68 0x118 0x68 0x68
  [ YP09.mkChunk 0x68 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x98 (CVal 8 (SOff 35 0));
    YP09.mkChunk 0xd0 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xe0 (CVal 8 (SOff 32 0xf8));
    YP09.mkChunk 0xf0 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x110 (CVal 8 (SOff 32 0xf0)) ].
Definition c1_rE1 : YP09.region := YP09.mkRegion (Some 32%nat) 0xf0 0xf8 0xf0 0xf8 [].
Definition c1_rE2 (n : Z) : YP09.region :=
  YP09.mkRegion (Some 32%nat) (0xf8 + n) (0xfb + n) (0xf8 + n) (0xfb + n) [YP09.mkChunk (0xf8 + n) (CZero 3)].
Definition c1_tf : facts := mkFacts [c1_fR; c1_fK; (32%nat, mkAF 4096 0x7fffff800000 5)] [] [].
Definition c1_tss (n : Z) : sstate := mkSS C1_MCR sr_atoms [c1_rTR; c1_rE1; c1_rE2 n] None c1_tf.
Definition c1_tx (F vb cur pp : Z) : list word :=
  [Z_to_bv 64 F; Z_to_bv 64 vb; Z_to_bv 64 cur; Z_to_bv 64 (pp + 0x4000); Z_to_bv 64 pp].
(* the five lengths of the vocab strings *)
Definition c1_lens : list Z := [12; 13; 14; 15; 18].
(* the bytes the tail writes; the stored size and second body byte by the kind's bit 7 *)
Definition c1_tail_wr (F n : Z) : Z -> Prop := fun a => (F + 0xf0 <= a < F + 0xf8) \/ (F + 0xf8 + n <= a < F + 0xfb + n).
Definition c1_ty (kd : Z) : Z := if kd <? 128 then 1 else 3.
Definition c1_xb (kd : Z) : Z := if kd <? 128 then 0 else 0x78.

Lemma c1_tss_wf : forall n, In n c1_lens -> regions_wf (ss_mem (c1_tss n)) = true.
Proof. intros n Hn. repeat (destruct Hn as [<-|Hn]; [vm_compute; reflexivity|]). destruct Hn. Qed.
(* `bgez s4` with s4 the kind byte sign-extended is taken exactly when bit 7 is clear *)
Lemma c1_bgez : forall E kd, ew E 20 = Z_to_bv 64 (kd - 256 * (kd / 128)) -> 0 <= kd < 256 ->
  branch_taken BC_GE (sv_denot E (SOff 20 0)) (sv_denot E (SLit 0)) = (kd <? 128).
Proof.
intros E kd H Hk. cbn [sv_denot]. rewrite H.
apply Bool.eqb_prop.
exact (c2_all256 (fun kd => Bool.eqb (branch_taken BC_GE (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (kd - 256 * (kd / 128))) + 0))
  (Z_to_bv 64 0)) (kd <? 128)) ltac:(vm_compute; reflexivity) kd Hk).
Qed.
Lemma c1_vm1_zero : forall m a, mbyte rsegs m a = Some (Z_to_bv 8 0) -> val_mem rsegs m a 1 0.
Proof. intros m a H k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r. exact H. Qed.

(* the windows of a state lie in Zn *)
Ltac c1_kwr2 B9 B32 :=
  let a := fresh "a" in let r0 := fresh "r0" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
  intros a (r0 & Hin & Hb);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r0 rs') in Hin end;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B9, ?B32 in Hb; unfold c1_tail_wr; lia|]);
  destruct Hin.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the shadow entry over e *)
Lemma c1_shok : forall (regs : bvmap 5 word) extra (H : word -> bool) mem F,
  getr regs 23 = w64 SHADOW_OFF -> nth 0 extra (Z_to_bv 64 0) = Z_to_bv 64 F -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0xf0) 104 ->
  (forall a, F + 0xf0 <= a < F + 0x158 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)) ->
  sh_ok rsegs EBx eb_SH (Ereg regs extra) (mrestrict H mem).
Proof.
intros regs extra H mem F H23 H32 HF1 HF2 Hra Hap. pose proof asan_consts as (Hceil & _).
assert (U23 : U (Ereg regs extra) (SOff 23 0) = SHADOW_OFF).
{ apply U_atom; [rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl), H23; reflexivity | unfold SHADOW_OFF; lia]. }
assert (U32 : U (Ereg regs extra) (SOff 32 0) = F).
{ apply U_atom; [rewrite (ew_Ereg_extra regs _ 0); exact H32 | lia]. }
apply Forall_cons; [|apply Forall_nil]. unfold shent_ok. cbn [she_m she_lo she_hi].
unfold EBx. rewrite U23, U32. split.
- rewrite <- (aview_rd_of rsegs). exact Hra.
- unfold app_apart. cbn [she_m she_lo she_hi]. unfold EBx. rewrite U23, U32. intros a Ha. apply Hap. lia.
Qed.

(* the entry state, for any length *)
Lemma c1_tail_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R F n vb cur pp,
  regions_wf (ss_mem (c1_tss n)) = true ->
  getr regs 9 = w64 R -> alloc_ceiling <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 ->
  getr regs 23 = w64 SHADOW_OFF ->
  4096 <= F -> F + 1024 <= alloc_ceiling -> F mod 32 = 0 -> 0 <= n <= 18 ->
  0 <= vb < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 vb ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xf8) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x68) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0xf0) ->
  (forall a, F + 0xf0 <= a < F + 0x158 -> apresent (w_H W) memc a) ->
  (forall i, 0 <= i < 3 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0xf8 + n + i) = Some (Z_to_bv 8 0)) ->
  st_ok rsegs (Ereg regs (c1_tx F vb cur pp)) (c1_tss n)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 C1_MCR) memc (seg_rom rsegs))).
Proof.
intros W regs memc R F n vb cur pp Hwf H9 HR1 HR2 HR3 H23 HF1 HF2 HF3 Hn Hvb Hcur Hpp1 Hpp2 V70 V80 Vb0 Vc0 Vc8 Vf0 Pe Ez.
pose proof asan_consts as (Hceil & _).
set (E := Ereg regs (c1_tx F vb cur pp)).
assert (B9 : bv_unsigned (ew E 9) = R) by exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (B23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by exact (eb_U_reg regs _ 23 23%bv _ eq_refl H23 ltac:(unfold SHADOW_OFF; lia)).
assert (B32 : bv_unsigned (ew E 32) = F) by exact (c1_U_extra regs (c1_tx F vb cur pp) 0 F eq_refl ltac:(lia)).
assert (B33 : bv_unsigned (ew E 33) = vb) by exact (c1_U_extra regs (c1_tx F vb cur pp) 1 vb eq_refl ltac:(lia)).
assert (B34 : bv_unsigned (ew E 34) = cur) by exact (c1_U_extra regs (c1_tx F vb cur pp) 2 cur eq_refl ltac:(lia)).
assert (B35 : bv_unsigned (ew E 35) = pp + 0x4000)
  by exact (c1_U_extra regs (c1_tx F vb cur pp) 3 (pp + 0x4000) eq_refl ltac:(lia)).
assert (B36 : bv_unsigned (ew E 36) = pp) by exact (c1_U_extra regs (c1_tx F vb cur pp) 4 pp eq_refl ltac:(lia)).
rewrite restrict_mkst_fx. unfold c1_tss. apply (entry_st_ok_full rsegs); try change (Ereg regs (c1_tx F vb cur pp)) with E.
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok, c1_rTR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs E _ R 0x68 8 (SOff 34 0) cur);
        [cbn [sv_denot]; rewrite B34, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vc8].
    * apply (chunk_ok_val rsegs E _ R 0x98 8 (SOff 35 0) (pp + 0x4000));
        [cbn [sv_denot]; rewrite B35, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V70].
    * apply (chunk_ok_val rsegs E _ R 0xd0 8 (SOff 33 0) vb);
        [cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vb0].
    * apply (chunk_ok_val rsegs E _ R 0xe0 8 (SOff 32 0xf8) (F + 0xf8));
        [cbn [sv_denot]; rewrite B32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vc0].
    * apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 36 0) pp);
        [cbn [sv_denot]; rewrite B36, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V80].
    * apply (chunk_ok_val rsegs E _ R 0x110 8 (SOff 32 0xf0) (F + 0xf0));
        [cbn [sv_denot]; rewrite B32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vf0].
  + unfold region_ok, c1_rE1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Pe. lia.
  + unfold region_ok, c1_rE2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B32. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply Pe; lia|].
    apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
    replace (F + (0xf8 + n) + i) with (F + 0xf8 + n + i) by lia. apply Ez. exact Hi.
- apply pairwise_disjoint_of_extents. unfold c1_rTR, c1_rE1, c1_rE2. cbn [map]. unfold extent_of_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite B9, B32. repeat split; first [exact I | lia].
- unfold facts_ok. cbn [c1_tf c1_fR c1_fK f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|split; [|split; [|exact I]]].
  + apply (c1_af _ _ R _ _ _ B9); [lia | change (2 ^ 4) with 16; exact HR3 | lia].
  + apply (c1_af _ _ SHADOW_OFF _ _ _ B23); [lia | reflexivity | lia].
  + apply (c1_af _ _ F _ _ _ B32); [lia | change (2 ^ 5) with 32; exact HF3 | lia].
Qed.

(* a zero byte of a CZero chunk of a run's last state *)
Lemma c1_zero_at : forall E ss H ms i r off len j a,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CZero len)) (YP09.r_chunks r) -> 0 <= j < len -> a = base_val E (YP09.r_base r) + off + j ->
  val_mem rsegs (mrestrict H (ms_mem ms)) a 1 0.
Proof.
intros E ss H ms i r off len j a HS Hi Hc Hj ->. apply c1_vm1_zero.
exact (eb_chunk_zero E _ r off len (eb_region E ss (restrict H ms) r HS (nth_error_In _ _ Hi)) Hc j Hj).
Qed.

(* the write windows of the tail: [R+0x68, R+0x118) is read only; e.type, e.size and e.body[len .. len + 3) lie in
   the frame (4, pos) the harness owns *)
Ltac c1_frame_awr pos Hown HFa :=
  cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  right; right; right; exists 4, pos; split; [exact Hown|]; left;
  unfold in_zr; cbn [fst snd]; rewrite <- HFa; change (fs_frame_bytes 4) with 1024; lia.
Ltac c1_awr B32 F pos Hown HFa :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat F); [reflexivity | exact B32 | c1_frame_awr pos Hown HFa |];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat F); [reflexivity | exact B32 | c1_frame_awr pos Hown HFa |];
  apply awr_ok_nil.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================================== c1_tail: 0x81fec .. J ======================================== *)
Lemma c1_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R F pos n kd vb cur pp,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  R mod 16 = 0 -> R + 0x1e0 <= sp0 -> sp0 - STK <= R - T_SEG_STK ->
  In (4, pos) own -> F = frame_addr lyc 4 pos ->
  In n c1_lens -> 0 <= kd < 256 ->
  getr regs 9 = w64 R -> getr regs 23 = w64 SHADOW_OFF -> getr regs 20 = w64 (kd - 256 * (kd / 128)) ->
  getr regs 21 = w64 n -> getr regs 24 = w64 (F + 0xf8) -> getr regs 25 = w64 n ->
  0 <= vb < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 vb ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xf8) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x68) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0xf0) ->
  (forall i, 0 <= i < 3 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0xf8 + n + i) = Some (Z_to_bv 8 0)) ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0xf0) 104 ->
  SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 C1_MCR) memc (seg_rom rsegs)) mdc)
  (w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W6_J regs memc mdc [10; 11; 12; 13; 20; 21; 24; 25; 27]%bv
   (c1_tail_wr F n)
   (fun regs2 mem2 => getr regs2 20 = w64 vb /\ getr regs2 21 = w64 (pp + 0x4000) /\ getr regs2 27 = w64 pp /\
     getr regs2 25 = w64 cur /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf0) 4 8 /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf4) 4 (n + c1_ty kd) /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf8 + n) 1 0 /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf8 + n + 1) 1 (c1_xb kd) /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf8 + n + 2) 1 0)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pos n kd vb cur pp HJ HR16 HRsp HspR Hown HFa Hn Hkd
  H9 H23 H20 H21 H24 H25 Hvb Hcur Hpp1 Hpp2 V70 V80 Vb0 Vc0 Vc8 Vf0 Ez Hrae.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
assert (HT : T_SEG_STK = 16384) by reflexivity. rewrite HT in HspR.
assert (HRb : alloc_ceiling <= R /\ R + 0x1e0 <= 2 ^ 47) by lia. destruct HRb as (HRb1 & HRb2).
clear Hsp0al Hceil Hslo Hshi H47.
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (HF32 & Happ & HFpres & _).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (HF4096 & HFceil & _).
rewrite <- HFa in HF32, Happ, HFpres, HF4096, HFceil.
change (fs_frame_bytes 4) with 1024 in Happ, HFpres, HFceil.
assert (Hn18 : 12 <= n <= 18) by (repeat (destruct Hn as [<-|Hn]; [lia|]); destruct Hn).
assert (Pe : forall a, F + 0xf0 <= a < F + 0x158 -> apresent (w_H W) memc a)
  by (intros a Ha; exact (proj1 (HFpres a ltac:(lia)))).
assert (Hap : forall a, F + 0xf0 <= a < F + 0x158 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)).
{ intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
pose proof (c1_tail_entry W regs memc R F n vb cur pp (c1_tss_wf n Hn) H9 HRb1 HRb2 HR16 H23 HF4096 HFceil HF32
  ltac:(lia) Hvb Hcur Hpp1 Hpp2 V70 V80 Vb0 Vc0 Vc8 Vf0 Pe Ez) as HS.
set (E := Ereg regs (c1_tx F vb cur pp)) in HS.
assert (B9 : bv_unsigned (ew E 9) = R) by exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (B32 : bv_unsigned (ew E 32) = F) by exact (c1_U_extra regs (c1_tx F vb cur pp) 0 F eq_refl ltac:(lia)).
assert (B33 : bv_unsigned (ew E 33) = vb) by exact (c1_U_extra regs (c1_tx F vb cur pp) 1 vb eq_refl ltac:(lia)).
assert (B34 : bv_unsigned (ew E 34) = cur) by exact (c1_U_extra regs (c1_tx F vb cur pp) 2 cur eq_refl ltac:(lia)).
assert (B35 : bv_unsigned (ew E 35) = pp + 0x4000)
  by exact (c1_U_extra regs (c1_tx F vb cur pp) 3 (pp + 0x4000) eq_refl ltac:(lia)).
assert (B36 : bv_unsigned (ew E 36) = pp) by exact (c1_U_extra regs (c1_tx F vb cur pp) 4 pp eq_refl ltac:(lia)).
assert (E20 : ew E 20 = Z_to_bv 64 (kd - 256 * (kd / 128))) by exact (eq_trans (ew_Ereg_nat regs _ 20 20%bv eq_refl) H20).
(* s5, s9 := the literal len; s8 := F + 0xf8 *)
pose proof (st_ok_pin_lit rsegs _ _ _ (21%bv : bv 5) n HS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H21; reflexivity)) as HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (25%bv : bv 5) n HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H25; reflexivity)) as HS2.
pose proof (st_ok_pin_sv rsegs _ _ _ (24%bv : bv 5) (SOff 32 0xf8) HS2 eq_refl
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite H24, B32; reflexivity)) as HS3.
clear HS HS1 HS2. rename HS3 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts c1_tss] in HS.
assert (SHOK : sh_ok rsegs EBx eb_SH E (mrestrict (w_H W) memc)).
{ apply (c1_shok regs (c1_tx F vb cur pp) (w_H W) memc F H23 eq_refl HF4096 HFceil Hrae Hap). }
assert (HAE : env_agree 32 E E) by apply env_agree_refl.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ c1_tail_wr F n a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
assert (Hgr0 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
clear Hfrs HFpres Pe Ez V70 V80 Vb0 Vc0 Vc8 Vf0 Hrae Hap Happ.
destruct Hn as [<-|[<-|[<-|[<-|[<-|[]]]]]];
(lazymatch type of HS with context [c1_rE2 ?n0] =>
 (* 0x81fec .. `bgez s4` 0x82008 *)
 aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan W6_J;
 [ c1_awr B32 F pos Hown HFa
 | lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end;
   pose proof (kept_run (c1_tail_wr F n0) _ _ (w_H W) memc memc (ms_mem ms1) KE HFr
     ltac:(c1_kwr2 B9 B32)) as KE1;
   clear KE HF HFr; rename KE1 into KE;
   pose proof (mem_grows_trans _ _ _ Hgr0 HG) as G1; clear Hgr0 HG; rename G1 into Hgr0;
   (* bit 7 of the kind: taken (clear) or not *)
   srr_branch_tok eb_tbl_ok HS SHOK Espan;
   (rewrite (c1_bgez _ kd E20 Hkd) in Hc; unfold c1_ty, c1_xb; rewrite Hc;
   aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan W6_J;
   [ c1_awr B32 F pos Hown HFa
   | lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ =>
     pose proof (kept_run (c1_tail_wr F n0) _ _ (w_H W) memc (ms_mem ms1) (ms_mem m) KE HFr
       ltac:(c1_kwr2 B9 B32)) as KE2;
     eapply (w7_post_of_run B);
     [ exact HS | reflexivity | reflexivity | exact HJ | c2_kio
     | eapply (HPgSteps.regs_kept_of_st_ok rsegs _ _ m regs (c1_tx F vb cur pp) (w_H W) _ HS);
         [env_agree_chain HAE | vm_compute; reflexivity]
     | exact KE2 | exact (mem_grows_trans _ _ _ Hgr0 HG) | ];
     cbv beta;
     split; [c1_reg HS (20%bv : bv 5); cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity|];
     split; [c1_reg HS (21%bv : bv 5); cbn [sv_denot]; rewrite B35, Z.add_0_r; reflexivity|];
     split; [c1_reg HS (27%bv : bv 5); cbn [sv_denot]; rewrite B36, Z.add_0_r; reflexivity|];
     split; [c1_reg HS (25%bv : bv 5); cbn [sv_denot]; rewrite B34, Z.add_0_r; reflexivity|];
     split; [eapply (tl_val_at _ _ (w_H W) m 1%nat _ 0xf0 4%N _ _ F _);
       [exact HS | reflexivity | c1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia]|];
     split; [eapply (tl_val_at _ _ (w_H W) m 1%nat _ 0xf4 4%N _ _ F _);
       [exact HS | reflexivity | c1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia]|];
     split; [eapply (tl_val_at _ _ (w_H W) m 2%nat _ (0xf8 + n0) 1%N _ _ F _);
       [exact HS | reflexivity | c1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia]|];
     lazymatch type of Hc with
     | _ = true =>
       split; [eapply (c1_zero_at _ _ (w_H W) m 2%nat _ (0xf9 + n0) 2 0 _);
         [exact HS | reflexivity | c1_in | lia | cbn [YP09.r_base base_val]; rewrite B32; lia]|];
       eapply (c1_zero_at _ _ (w_H W) m 2%nat _ (0xf9 + n0) 2 1 _);
         [exact HS | reflexivity | c1_in | lia | cbn [YP09.r_base base_val]; rewrite B32; lia]
     | _ = false =>
       split; [eapply (tl_val_at _ _ (w_H W) m 2%nat _ (0xf9 + n0) 1%N _ _ F _);
         [exact HS | reflexivity | c1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia]|];
       eapply (tl_val_at _ _ (w_H W) m 2%nat _ (0xfa + n0) 1%N _ _ F _);
         [exact HS | reflexivity | c1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia]
     end
     end ]) ]
 end).
Qed.
End d.
End b.

Print Assumptions c1_tail.
