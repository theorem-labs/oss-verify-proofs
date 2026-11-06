(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkE.v at 4ae09a76d9d; its block E2 walked
   again on fuzz_headamp.asan-ubsan's own code (&e62 arrives in s4, the reloads are a3 := R+0x110, s7 := R+0x148 and
   t1 := s5), the post HPgCaseB.cb_post, the statement HPgW7bBase.hw7b_E2_stmt, RPgMem.rm_ -> HPgMem.hm_,
   w7_ / e2_ -> hw7b_, module paths. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): block E2 of the walk of
   LLVMFuzzerTestOneInput from G 0x81afc to J 0x82618 (lib/AU/HPgW7bBase.v). Proves no function (kind: segment
   lemma).

   E2, 0x81c08 .. 0x81c64 (pod.h:258-262):
     sb zero,0(a0)                      the NUL at xb = e62.body + n (a0, atom 32)
     li a0,8; sw a0,0(s4); sw s10,4(s4) e62.type = 8, e62.size = m = n + 1 at ea = &e62 (s4, atom 20)
     li a0,-8; sb a0 at s3 + 0x14..0x16, 8..0xb, 4..7, 0xc..0xf
                                        ch and t out of scope: 15 shadow bytes 0xf8 of the frame for locals sF (s3)
     ld a3,0x110(s1); ld s7,0x148(s1); mv t1,s5; j 0x82618
   No instrumented check, so the plain runner (YCbq.v aj_run_to) runs it. The two 8-byte frame cells R+0x110 (the
   cursor vcur) and R+0x148 (pp, vpp) are read-only chunks of a region at atom 9 = R holding the extra atoms 33 and
   34. The write windows are xb, [ea, ea + 8), [sF + 4, sF + 0x10) and [sF + 0x14, sF + 0x17), writable from the
   lemma's awr_byte premises through the journal (awr_byte_present).
   REGISTERS: a0 (x10), a3 (x13), t1 (x6), s1 = R (x9), s3 = sF (x19), s4 = ea (x20), s5 (x21), s7 (x23), s10 = m
   (x26); CELLS read: R+0x110, R+0x148; none written. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgPropKit HPgW7bBase HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the start: a0 = xb (atom 32); the regions the block reads and writes *)
Definition e2_regions : smem :=
[ YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
  YP09.mkRegion (Some 9%nat) 0x110 0x150 0 0
    [YP09.mkChunk 0x110 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x148 (CVal 8 (SOff 34 0))];
  YP09.mkRegion (Some 20%nat) 0 8 0 8 [];
  YP09.mkRegion (Some 19%nat) 4 0x10 4 0x10 [];
  YP09.mkRegion (Some 19%nat) 0x14 0x17 0x14 0x17 [] ].
Definition ss_E2 : sstate :=
mkSS HW7B_E2 (sr_set sr_atoms 10%bv (SOff 32 0)) e2_regions None (mkFacts [] [] []).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* an atom's symbolic value *)
Lemma hw7b_e2_den : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv.
rewrite Z.add_0_r. reflexivity.
Qed.
Lemma hw7b_e2_den_reg : forall E n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* the byte a one-byte chunk of a region holds, as aview sees it *)
Lemma hw7b_e2_view1 : forall E (H : word -> bool) mem n b lo hi wlo whi cs off e v,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 1 e)) cs ->
bv_unsigned (sv_denot E e) mod 256 = v ->
aview rsegs H mem (b + off) = Some v.
Proof.
intros E H mem n b lo hi wlo whi cs off e v (_ & _ & _ & Hcs) Hn Hc Hv.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bt & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. rewrite Z.add_0_r in Hm.
injection Hb as Hb. subst bt.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r, HPgMem.hm_unsigned_byte. exact Hv.
Qed.
(* the same with the chunk found by a closed boolean search, which vm_compute decides *)
Lemma hw7b_e2_view1b : forall E (H : word -> bool) mem n b lo hi wlo whi cs off v,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b ->
existsb (fun c => (YP09.c_off c =? off) && match YP09.c_val c with
  | CVal w e => (w =? 1)%N && (bv_unsigned (sv_denot E e) mod 256 =? v) | _ => false end) cs = true ->
aview rsegs H mem (b + off) = Some v.
Proof.
intros E H mem n b lo hi wlo whi cs off v Hr Hn Hex.
apply existsb_exists in Hex as ([o cv] & Hc & Hb). cbn [YP09.c_off YP09.c_val] in Hb.
apply andb_prop in Hb as [Ho Hb]. apply Z.eqb_eq in Ho. subst o.
destruct cv as [w e|l|l|d s l]; try discriminate Hb.
apply andb_prop in Hb as [Hw Hv]. apply N.eqb_eq in Hw. subst w. apply Z.eqb_eq in Hv.
exact (hw7b_e2_view1 E H mem n b lo hi wlo whi cs off e v Hr Hn Hc Hv).
Qed.

(* the region i of a state the engine left *)
Ltac e2_rnth HS i Hr :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let o := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch o with Some ?r =>
let Hn := fresh "Hn" in
assert (Hn : nth_error (ss_mem ss) i = Some r) by (vm_compute; reflexivity);
pose proof (hw7b_region_nth _ _ _ i r HS Hn) as Hr; clear Hn; cbn [restrict ms_mem] in Hr
end end.
(* a register's symbolic value at the engine's last state *)
Ltac e2_getr HS r :=
rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS);
lazymatch type of HS with st_ok _ _ ?ssv _ =>
let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end.
(* a byte 0xf8 of the shadow of t and ch at sF + i, out of region Hr *)
Ltac e2_sh Hr B19 :=
apply (hw7b_e2_view1b _ _ _ 19%nat _ _ _ _ _ _ _ _ Hr B19); vm_compute; reflexivity.
(* a property of every integer of [lo, lo + n), from one goal per integer *)
Lemma hw7b_e2_range : forall (P : Z -> Prop) lo n, (forall j, (j < n)%nat -> P (lo + Z.of_nat j)) ->
forall i, lo <= i < lo + Z.of_nat n -> P i.
Proof.
intros P lo n H i Hi. replace i with (lo + Z.of_nat (Z.to_nat (i - lo))) by lia. apply H. lia.
Qed.
(* the literal offset lo + j of one such goal *)
Ltac e2_off :=
cbv beta; lazymatch goal with |- context [?a + Z.of_nat ?j] =>
let v := eval vm_compute in (a + Z.of_nat j) in change (a + Z.of_nat j) with v end.

Lemma hw7b_E2 : forall B, hw7b_E2_stmt B.
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R sF xb ea m lv vcur vpp
HJ H10 H9 HR0 HR1 HR16 H19 H20 H26 Hm H21 Vcur Hvcur Vpp Hvpp Hea0 Hea Hxb HsF0 HsF HsFR Wxb Wea WsF.
pose proof (AR_laws_ok rsegs B) as LAWS.
clear HR16.
pose proof hw7b_wx as Hwx. pose proof hw7b_segs_low as Hsegs.
assert (P : forall a, awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a -> apresent (w_H W) memc a).
{ intros a Ha.
  first [ exact (proj1 (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Ha))
        | exact (proj1 (awr_byte_present rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Ha)) ]. }
remember (Ereg regs [w64 xb; w64 vcur; w64 vpp]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [w64 xb; w64 vcur; w64 vpp]) E) by (subst E; apply env_agree_refl).
assert (E32 : ew E 32 = w64 xb) by (subst E; reflexivity).
assert (E33 : ew E 33 = w64 vcur) by (subst E; reflexivity).
assert (E34 : ew E 34 = w64 vpp) by (subst E; reflexivity).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = w64 sF) by (subst E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = w64 ea) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = w64 lv) by (subst E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E26 : ew E 26 = w64 m) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (B32 : bv_unsigned (ew E 32) = xb) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (B20 : bv_unsigned (ew E 20) = ea) by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew E 9) = R) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (B19 : bv_unsigned (ew E 19) = sF) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ss_E2 (restrict (w_H W) (mkst regs (Z_to_bv 64 HW7B_E2) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_E2. rewrite HE. apply (entry_st_ok_full rsegs); try rewrite <- HE.
  - apply YI04.regs_ok_pin; [rewrite HE; apply regs_ok_Ereg | intros X; discriminate X |].
    rewrite H10. symmetry. apply hw7b_e2_den; [exact E32 | lia].
  - vm_compute. reflexivity.
  - unfold e2_regions.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
    + apply (HPgMem.hm_rw_region rsegs _ _ _ 32%nat xb); [exact B32 | lia | lia | | apply Forall_nil].
      intros o Ho. replace (xb + o) with xb by lia. exact (P xb Wxb).
    + apply (HPgMem.hm_ro_region rsegs _ _ _ 9%nat R); [exact B9 | lia | lia |].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ vcur); [exact (hw7b_e2_den _ 33 vcur E33 Hvcur) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vcur].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ vpp); [exact (hw7b_e2_den _ 34 vpp E34 Hvpp) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vpp].
    + apply (HPgMem.hm_rw_region rsegs _ _ _ 20%nat ea); [exact B20 | lia | lia | | apply Forall_nil].
      intros o Ho. apply P, Wea. lia.
    + apply (HPgMem.hm_rw_region rsegs _ _ _ 19%nat sF); [exact B19 | lia | lia | | apply Forall_nil].
      intros o Ho. apply P, WsF. lia.
    + apply (HPgMem.hm_rw_region rsegs _ _ _ 19%nat sF); [exact B19 | lia | lia | | apply Forall_nil].
      intros o Ho. apply P, WsF. lia.
  - unfold e2_regions.
    cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite B32, B9, B20, B19. repeat split; lia.
  - split; [exact I | split; exact I]. }
clear HE.
(* 0x81c08 .. 0x81c64: the NUL; e62.type = 8; e62.size = m; the 15 shadow bytes 0xf8; the reloads; j 0x82618 *)
aj_run_to hw7b_tbl_ok HS HJ HW7B_J.
- change (ss_mem ss_E2) with e2_regions. unfold e2_regions.
  apply (hw7b_awr_cons E _ _ _ _ _ _ _ _ _ 32%nat xb); [reflexivity | exact B32 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with xb by lia. exact Wxb. }
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |].
  apply (hw7b_awr_cons E _ _ _ _ _ _ _ _ _ 20%nat ea); [reflexivity | exact B20 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply Wea. lia. }
  apply (hw7b_awr_cons E _ _ _ _ _ _ _ _ _ 19%nat sF); [reflexivity | exact B19 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply WsF. lia. }
  apply (hw7b_awr_cons E _ _ _ _ _ _ _ _ _ 19%nat sF); [reflexivity | exact B19 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply WsF. lia. }
  apply awr_ok_nil.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [w64 xb; w64 vcur; w64 vpp] (w_H W) _ HS);
      [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz.
    refine (cb_kept_run
      (fun a => a = xb \/ ea <= a < ea + 8 \/ sF + 4 <= a < sF + 0x10 \/ sF + 0x14 <= a < sF + 0x17)
      E _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr _ a Ha Hz).
    intros x (r & Hr & Hb). change (ss_mem ss_E2) with e2_regions in Hr. unfold e2_regions in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B32, ?B9, ?B20, ?B19 in Hb; cbv beta; lia.
  + cbv beta.
    e2_rnth HS 0%nat Hr0. e2_rnth HS 2%nat Hr2. e2_rnth HS 3%nat Hr3. e2_rnth HS 4%nat Hr4.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    * e2_getr HS (13%bv : bv 5). exact (hw7b_e2_den E 33 vcur E33 Hvcur).
    * e2_getr HS (23%bv : bv 5). exact (hw7b_e2_den E 34 vpp E34 Hvpp).
    * e2_getr HS (6%bv : bv 5). exact (hw7b_e2_den_reg E 21 _ E21).
    * rewrite <- (Z.add_0_r xb).
      apply (hw7b_e2_view1b _ _ _ 32%nat _ _ _ _ _ _ _ _ Hr0 B32). vm_compute. reflexivity.
    * pose proof (hw7b_field E _ 20%nat ea _ _ _ _ _ 0 4 (SLit 8) 8 Hr2 B20
        ltac:(cbv [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
      rewrite Z.add_0_r in V. exact V.
    * exact (hw7b_field E _ 20%nat ea _ _ _ _ _ 4 4 (SOff 26 0) m Hr2 B20
        ltac:(cbv [In]; repeat (first [left; reflexivity | right])) (hw7b_e2_den_reg E 26 _ E26)
        ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)).
    * intros i [Hi|Hi]; revert i Hi.
      { refine (hw7b_e2_range (fun i => aview rsegs (w_H W) (ms_mem ms) (sF + i) = Some 248) 4 12 _).
        intros j Hj. do 12 (destruct j as [|j]; [e2_off; e2_sh Hr3 B19 |]). lia. }
      { refine (hw7b_e2_range (fun i => aview rsegs (w_H W) (ms_mem ms) (sF + i) = Some 248) 20 3 _).
        intros j Hj. do 3 (destruct j as [|j]; [e2_off; e2_sh Hr4 B19 |]). lia. }
Qed.
End b.

Print Assumptions hw7b_E2.
