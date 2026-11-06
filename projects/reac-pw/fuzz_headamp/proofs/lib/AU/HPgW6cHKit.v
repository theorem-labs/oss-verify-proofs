(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the kit the heads of ent_build's cases 6 and 8
   share inside LLVMFuzzerTestOneInput (0x80c40). Proves no function (kind: segment lemma).

   Both heads read a 16-byte table of .rodata (ent_build.t 0x21120, ent_build.t.11 0x21140) at an index t & 3 of the
   input byte t. The input may lie anywhere the contract allows, the image included, so the table's region
   (HPgW6cEng.w6c_RT) and the input's never share one engine state: after the input byte is read the input region is
   dropped (w6c_drop3), the table's added (w6c_add_RT; e62 and R's cells lie apart from the image, w6c_RT_apart), the
   index's register pinned to each of its four values, and for case 8's second byte the table dropped again and one
   input byte added back (w6c_RI2, w6c_add_RI2). A head's regions write e62.type only (w6c_rokb, w6c_hawr, w6c_hw). *)
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
  HPgW6cEng HPgW6cCase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the write windows of a head's regions: none, or e62.type ---- *)
Definition w6c_rokb (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  match YP09.r_base r with
  | Some n => Nat.eqb n 32 && (YP09.r_wlo r =? 0x210) && (YP09.r_whi r =? 0x214)
  | None => false
  end.
Lemma w6c_hw : forall E (l rs : smem) a, YP09.skeleton rs = YP09.skeleton l -> forallb w6c_rokb l = true ->
  in_wrange E rs a -> bv_unsigned (ew E 32) + 0x210 <= a < bv_unsigned (ew E 32) + 0x214.
Proof.
intros E l rs a Hsk Hl Ha. apply (in_wrange_skeleton E rs l a Hsk) in Ha. destruct Ha as (r & Hin & Ha).
pose proof (proj1 (forallb_forall _ _) Hl r Hin) as Hr. unfold w6c_rokb in Hr.
apply orb_true_iff in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate].
apply andb_true_iff in Hr as [Hr H2]. apply andb_true_iff in Hr as [H0 H1].
apply Nat.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst n.
try rewrite Eb in Ha. cbn [base_val] in Ha. lia.
Qed.
Lemma w6c_hawr : forall E (l rs : smem) STK sp0 FP bl0 blc lyc own F pos,
  YP09.skeleton rs = YP09.skeleton l -> forallb w6c_rokb l = true ->
  bv_unsigned (ew E 32) = F -> In (4, pos) own -> F = frame_addr lyc 4 pos ->
  awr_ok E rs STK sp0 FP bl0 blc lyc own.
Proof.
intros E l rs STK sp0 FP bl0 blc lyc own F pos Hsk Hl U32 Hown HF a Ha.
pose proof (w6c_hw E l rs a Hsk Hl Ha) as Hw. rewrite U32 in Hw.
unfold awr_byte. right; right; right. exists 4, pos. split; [exact Hown|]. left.
unfold in_zr. cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* ---- regions in and out ---- *)
Lemma w6c_drop3 : forall E pc rg r1 r2 r3 resv f ms,
  st_ok rsegs E (mkSS pc rg [r1; r2; r3] resv f) ms -> st_ok rsegs E (mkSS pc rg [r1; r2] resv f) ms.
Proof. intros E pc rg r1 r2 r3 resv f ms HS. exact (w6c_st_ok_drop E pc rg [r1; r2] r3 resv f ms HS). Qed.
Lemma w6c_apart_img : forall lo1 hi1 lo2 hi2, lo1 < hi1 -> lo2 < hi2 ->
  (forall a, lo1 <= a < hi1 -> ~ in_img rsegs a) -> (forall a, lo2 <= a < hi2 -> in_img rsegs a) ->
  hi1 <= lo2 \/ hi2 <= lo1.
Proof.
intros lo1 hi1 lo2 hi2 H1 H2 Hn Hi. destruct (Z_le_gt_dec hi1 lo2) as [X|X]; [left; exact X|].
destruct (Z_le_gt_dec hi2 lo1) as [Y|Y]; [right; exact Y|].
exfalso. apply (Hn (Z.max lo1 lo2)); [lia|]. apply Hi. lia.
Qed.
(* the table's region added to a state holding R's cells and e62's header *)
Lemma w6c_add_RT : forall E pc rg r1 r2 resv f (W : world rsegs) ms tb R F,
  st_ok rsegs E (mkSS pc rg [r1; r2] resv f) (restrict (w_H W) ms) ->
  YP09.r_base r1 = Some 9%nat -> YP09.r_lo r1 = 0x10 -> YP09.r_hi r1 = 0x150 ->
  YP09.r_base r2 = Some 32%nat -> YP09.r_lo r2 = 0x210 -> YP09.r_hi r2 = 0x218 ->
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> 0x10007fffc000 <= R ->
  (forall a, F + 0x210 <= a < F + 0x218 -> ~ in_img rsegs a) ->
  rom_view rsegs W (ms_mem ms) -> cj_in_seg_b tb (tb + 16) = true -> rom_run_b tb 16 = true -> 0 <= tb <= 0x100000 ->
  YP09.region_wf (w6c_RT tb) = true ->
  st_ok rsegs E (mkSS pc rg [r1; r2; w6c_RT tb] resv f) (restrict (w_H W) ms).
Proof.
intros E pc rg r1 r2 resv f W ms tb R F HS B1 L1 H1 B2 L2 H2 U9 U32 HR Hni Hrom Hseg Hrun Htb Hwf.
apply (w6c_st_ok_add E pc rg [r1; r2] (w6c_RT tb) resv f _ HS).
- exact Hwf.
- cbn [restrict ms_mem]. apply img_region_ok_rom; [exact Hrom | lia | lia | lia | exact Hrun].
- repeat apply Forall_cons; try apply Forall_nil; unfold extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val w6c_RT]; rewrite ?B1, ?L1, ?H1, ?B2, ?L2, ?H2; cbn [base_val];
    rewrite ?U9, ?U32.
  + lia.
  + apply (w6c_apart_img (F + 0x210) (F + 0x218) (0 + tb) (0 + tb + 16)); [lia | lia | exact Hni|].
    intros a Ha. apply (cj_in_seg tb (tb + 16) a Hseg). lia.
Qed.
Lemma w6c_rom_tb6_seg : cj_in_seg_b W6C_TB6 (W6C_TB6 + 16) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w6c_rom_tb8_seg : cj_in_seg_b W6C_TB8 (W6C_TB8 + 16) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w6c_RT6_wf : YP09.region_wf (w6c_RT W6C_TB6) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w6c_RT8_wf : YP09.region_wf (w6c_RT W6C_TB8) = true.
Proof. vm_compute. reflexivity. Qed.

(* one input byte, the second after the kind byte, in a region based on a7 = cur - 1 *)
Definition w6c_RI2 : YP09.region := YP09.mkRegion (Some 17%nat) 2 3 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 34 0))].
Lemma w6c_add_RI2 : forall E pc rg r1 r2 resv f (W : world rsegs) ms R F c1 s,
  st_ok rsegs E (mkSS pc rg [r1; r2] resv f) (restrict (w_H W) ms) ->
  YP09.r_base r1 = Some 9%nat -> YP09.r_lo r1 = 0x10 -> YP09.r_hi r1 = 0x150 ->
  YP09.r_base r2 = Some 32%nat -> YP09.r_lo r2 = 0x210 -> YP09.r_hi r2 = 0x218 ->
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> bv_unsigned (ew E 17) = c1 -> ew E 34 = Z_to_bv 64 s ->
  0 <= s < 256 -> 0 <= c1 -> c1 + 3 <= 2 ^ 64 ->
  ~ (R <= c1 + 2 < R + 0x198) -> ~ (F + 0x20 <= c1 + 2 < F + 0x278) ->
  val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (c1 + 2) 1 s ->
  st_ok rsegs E (mkSS pc rg [r1; r2; w6c_RI2] resv f) (restrict (w_H W) ms).
Proof.
intros E pc rg r1 r2 resv f W ms R F c1 s HS B1 L1 H1 B2 L2 H2 U9 U32 U17 E34 Hs Hc1 Hc3 D1 D2 V.
apply (w6c_st_ok_add E pc rg [r1; r2] w6c_RI2 resv f _ HS).
- vm_compute. reflexivity.
- cbn [restrict ms_mem]. unfold w6c_RI2. apply (hm_ro_region rsegs E (w_H W) (ms_mem ms) 17%nat c1); [exact U17 | lia | lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs E _ c1 2 1 (SOff 34 0) s); [| cbn; lia | lia | exact V].
  cbn [sv_denot]. rewrite E34, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val w6c_RI2]; rewrite ?B1, ?L1, ?H1, ?B2, ?L2, ?H2; cbn [base_val];
    rewrite ?U9, ?U32, ?U17; lia.
Qed.

(* ---- the frame lies apart from the image ---- *)
Lemma w6c_frame_not_img : forall (B : asyms) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc F pos,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (4, pos) own -> F = frame_addr lyc 4 pos ->
  forall a, F <= a < F + 1024 -> ~ in_img rsegs a.
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc F pos HJ Hown HF a Ha.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
refine (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR _)).
right; left. exists 4, pos. split; [exact Hin4|]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
Qed.
End b.

(* ---- moving facts across a run ---- *)
(* the frame's presence across a run that grows the memory *)
Ltac w6c_pres P :=
  lazymatch goal with
  | HGx : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2), P0 : forall o, _ -> apresent ?H ?m1 _ |- _ =>
    let P' := fresh "P'" in
    pose proof (fun o Ho => apresent_grows H m1 m2 _ HGx (P0 o Ho)) as P';
    clear P0 HGx; rename P' into P
  end.

Print Assumptions w6c_hw.
Print Assumptions w6c_hawr.
Print Assumptions w6c_drop3.
Print Assumptions w6c_add_RT.
Print Assumptions w6c_add_RI2.
Print Assumptions w6c_frame_not_img.
