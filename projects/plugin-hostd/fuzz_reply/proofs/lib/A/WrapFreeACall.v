(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: RELOCATED to the #102 pins (image A' = asan 1be0f53d96cb, twin bff8519bbe3e) from a working branch cb44bc9b99c (old-pin image A) by the relocation script reloc_A2.py (named with its outputs in the commit that added this line): every code address moved by symbol + offset (reloc_A2.out), the walk's functions checked by bytecmp 1480ca2faea0 + a target pass (measure_A2.out); data addresses come by name from int102's A' tables; ARXs_cf / ARmcf follow a Theorem Labs lane's a2b14794b6e6 (xs_placed is ARmcf's field amc_xs_placed). *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFh1.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/AFh1.v segN (the free interceptor's NULL-site walk) as the CALL SEGMENT of the image-A free interceptor walk over ARcf (a Theorem Labs lane's Record wrap_free_walk_cf): __wrap_free's entry 0x53de8 to Deallocate's entry 0x318c4, for a symbolic freed pointer p over lib/A/WrapFreeAEnv.v. The changes:
   the level-1 map cell region is the atom-37 region (TFIB_IAL_LO + 8 * (p / 2 ^ 32), WrapFreeAEnv.EaIM) in place of AFfx.R_IMN;
   a1 = p >> 47 and a2 = atom 37 are pinned after 0x53e28 and at 0x53e3c as lib/A/AFga.v:264-275 does;
   after the unwinder's return the run stops at Deallocate's entry 0x318c4 (through 0x53f88-0x53f98 and asan_free 0x3189c-0x318c0),
   and at_DEALLOC is proved from that state as lib/AU/WrapMallocBCall.v:430-508 (a working branch) proves its at_ALLOC. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require WrapFreeAEnv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variable p : Z.
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x53de8) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : WrapFreeAEnv.free_hyps W ly regs0 mem0 ch p ii.
Local Notation tr := (WrapFreeAEnv.tr ly regs0 ch).
Local Notation LENv := (WrapFreeAEnv.LENv ly regs0 ch).
Local Notation E0 := (WrapFreeAEnv.E0 ly regs0 ch p).
Local Notation Er := (WrapFreeAEnv.Er ly regs0 ch p).
Local Notation E2 := (WrapFreeAEnv.E2 ly regs0 ch p).
Local Notation E1 := (WrapFreeAEnv.E1 ly regs0 ch p).
Local Notation E8 := (WrapFreeAEnv.E8 ly regs0 ch p).
Local Notation E10 := (WrapFreeAEnv.E10 ly regs0 ch p).
Local Notation EaT := (WrapFreeAEnv.EaT ly regs0 ch p).
Local Notation EaC := (WrapFreeAEnv.EaC ly regs0 ch p).
Local Notation EaTOP := (WrapFreeAEnv.EaTOP ly regs0 ch p).
Local Notation EaIM := (WrapFreeAEnv.EaIM ly regs0 ch p).
Local Notation SS0 := WrapFreeAEnv.SS0.
Local Notation LYB := (WrapFreeAEnv.LYB W ly regs0 mem0 ch p ii FH).
Local Notation stack_ivs := (WrapFreeAEnv.stack_ivs W ly regs0 mem0 ch p ii FH).
Local Notation windows_WIN := (WrapFreeAEnv.windows_WIN W ly regs0 mem0 ch p ii FH).
Local Notation WIN_zone := (WrapFreeAEnv.WIN_zone W ly regs0 mem0 ch p ii FH).
Local Notation WIN_not_high := (WrapFreeAEnv.WIN_not_high W ly regs0 mem0 ch p ii FH).
Local Notation all_disjoint_of_forall := (WrapFreeAEnv.all_disjoint_of_forall W ly regs0 mem0 ch p ii FH).
Local Notation kept_of_frame := (WrapFreeAEnv.kept_of_frame W ly regs0 mem0 ch p ii FH).
Local Notation kept_of_frame_hi := (WrapFreeAEnv.kept_of_frame_hi W ly regs0 mem0 ch p ii FH).
Local Notation SKEL_TAIL := WrapFreeAEnv.SKEL_TAIL.
Local Notation IZONE := WrapFreeAEnv.IZONE.
Local Notation tail_facts := (WrapFreeAEnv.tail_facts W ly regs0 mem0 ch p ii FH).
Local Notation MEQI := (WrapFreeAEnv.MEQI W ly regs0 mem0).
Local Notation MEQI_frame := (WrapFreeAEnv.MEQI_frame W ly regs0 mem0 ch p ii FH).
Local Notation off_T := (WrapFreeAEnv.off_T W ly regs0 mem0 ch p ii FH).
Local Notation off_C := (WrapFreeAEnv.off_C W ly regs0 mem0 ch p ii FH).
Local Notation off_NB := (WrapFreeAEnv.off_NB W ly regs0 mem0 ch p ii FH).
Local Notation off_SB := (WrapFreeAEnv.off_SB W ly regs0 mem0 ch p ii FH).
Local Notation pres_off_of_frame := (WrapFreeAEnv.pres_off_of_frame W).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac | apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac open_FH :=
pose proof (@WrapFreeAEnv.fh_LY _ _ _ _ _ _ _ _ _ FH) as LY;
pose proof (@WrapFreeAEnv.fh_IMG _ _ _ _ _ _ _ _ _ FH) as IMG;
pose proof (@WrapFreeAEnv.fh_Hp10 _ _ _ _ _ _ _ _ _ FH) as Hp10;
pose proof (@WrapFreeAEnv.fh_Hp47 _ _ _ _ _ _ _ _ _ FH) as Hp47;
pose proof (@WrapFreeAEnv.fh_Htp _ _ _ _ _ _ _ _ _ FH) as Htp;
pose proof (@WrapFreeAEnv.fh_Hra _ _ _ _ _ _ _ _ _ FH) as Hra;
pose proof (@WrapFreeAEnv.fh_Hra4096 _ _ _ _ _ _ _ _ _ FH) as Hra4096;
pose proof (@WrapFreeAEnv.fh_Hsp _ _ _ _ _ _ _ _ _ FH) as Hsp;
pose proof (@WrapFreeAEnv.fh_Hsp_al _ _ _ _ _ _ _ _ _ FH) as Hsp_al;
pose proof (@WrapFreeAEnv.fh_Hch _ _ _ _ _ _ _ _ _ FH) as Hch;
pose proof (@WrapFreeAEnv.fh_HIAL _ _ _ _ _ _ _ _ _ FH) as HIAL;
pose proof (@WrapFreeAEnv.fh_IA1 _ _ _ _ _ _ _ _ _ FH) as IA1;
pose proof (@WrapFreeAEnv.fh_U1 _ _ _ _ _ _ _ _ _ FH) as U1;
pose proof (@WrapFreeAEnv.fh_SEED _ _ _ _ _ _ _ _ _ FH) as SEED.
Ltac meq_acc HE :=
match goal with
| M : MEQI ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQI_frame E rs ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Definition at_DEALLOC (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regsD memD mat,
c' = mkCfg (mkst regsD (w64 0x318c4) memD (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regsD 1 = w64 0x53f9c /\ getr regsD 2 = w64 (sp0 - 2128) /\
getr regsD 10 = w64 TFIB_INST /\ getr regsD 11 = getr regs0 10 /\ getr regsD 12 = w64 0 /\ getr regsD 13 = w64 0 /\
getr regsD 14 = w64 (sp0 - 2128) /\ getr regsD 15 = w64 1 /\
getr regsD 3 = getr regs0 3 /\ getr regsD 4 = w64 TFIB_TP /\
(forall r : Z, 22 <= r <= 27 -> getr regsD (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) /\
WrapFreeAEnv.MEQI W ly regs0 mem0 memD /\
val_mem tfibsegs (mrestrict (w_H W) memD) (T + t_unwinding) 1 0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) memD a) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 2128) 8 (sp0 - 2112) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 2120) 8 (WrapFreeAEnv.LENv ly regs0 ch) /\
(forall i, (i < length (WrapFreeAEnv.tr ly regs0 ch))%nat ->
  val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 2112 + 8 * Z.of_nat i) 8 (nth i (WrapFreeAEnv.tr ly regs0 ch) 0)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 56) 8 (bv_unsigned (getr regs0 21)).
Lemma seg_call : SRr tfibsegs W cfg0 at_DEALLOC.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
(* AFh1.v:124-148: the run to internal_allocator and its spec. *)
srr_run_to_sh tfibtbl_rtF_ok HS 0x5f704.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
eapply SRr_bind.
{ destruct HIAL as (IA & IB & IC & ID).
assert (FR : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ms_mem ms (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha. apply HF. intros Hw.
lazymatch type of Hw with in_wrange _ ?rs _ =>
pose proof (WIN_zone _ (windows_WIN E0 rs _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw)) as (X & _) end.
rewrite unsigned_lit_small in X by (unfold TFIB_IMG_LO, TFIB_IMG_END in Ha; zlia). exact (X Ha). }
apply (IA1 W (ms_regs ms) (ms_mem ms) _ ii).
- rreg HS (1%bv : bv 5) R1; rewrite R1. apply YK0s.ret_ok_even. reflexivity.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; zlia).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; zlia). numconst; zlia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; zlia). numconst; zlia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (numconst; zlia).
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; numconst; zlia
| off_by ltac:(numconst; zlia) ].
- eapply val_mem_frame; [|exact IA]. intros k Hk. apply FR; numconst; zlia.
- eapply val_mem_frame; [|exact IB]. intros k Hk. apply FR; numconst; zlia.
- memv HS 21%nat 0%nat; [reflexivity | reflexivity | zlia].
- memv HS 22%nat 0%nat; [reflexivity | reflexivity | zlia].
- destruct ii; destruct IC as [IC1 IC2]; split; (eapply val_mem_frame; [|eassumption]); intros k Hk; apply FR; numconst; zlia.
- intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) mem0 (ms_mem ms) a) by (apply FR; numconst; zlia). apply ID. exact Ha. }
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & H10r & Hfr & Hpr & IV1 & IV2 & IV3 & IV4 & IV5). srr_norm_model.
(* AFh1.v:150-184: the return from internal_allocator; the frame and scratch regions. *)
rreg HS (1%bv : bv 5) R1.
set (X1 := fun a : Z => (sp0 - 2176 <= a < sp0 - 2128) \/ IZONE a).
assert (Hfr' : forall x : word, ~ X1 (bv_unsigned x) -> mem1 x = ms_mem ms x).
{ intros x Hx. subst X1. unfold IZONE in Hx. rewrite R2 in Hfr. unfold w64 in Hfr. rewrite unsigned_lit_small in Hfr by (numconst; zlia).
apply Hfr; unfold IAL_STK in *; tauto || (intros HH; apply Hx; tauto) || zlia. }
jafter_call2 HS 54%nat regs1 (mrestrict (w_H W) mem1) HP (-2128) (seq 0 36) HS1.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ constructor;
[ eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:(subst X1; unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; zlia) Hpr)); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite E2; subst X1; unfold IZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; zlia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts E0 r (fun k _ => eq_refl) Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:(subst X1; unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; zlia) Hpr)); intros a Ha; subst X1; unfold IZONE; cbn beta; clear - Ha Y1 Y2 Y3 Y4 Y5; numconst; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. apply Hpr; [clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia|]. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; numconst; zlia | off_by ltac:(numconst; zlia) ]. }
set (En1 := havoc E0 54 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < aHAVf)%nat -> ew En1 k = ew E0 k) by (intros k Hk; subst En1; apply ew_havoc_old; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold IFRAME;
split; [numconst; zlia|]; split; [numconst; zlia|]; split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(numconst; zlia) | apply PRES1; numconst; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
(* AFga.v:237-253: the level-1 map cell region at atom 37 (TFIB_IAL_LO + 8 * (p / 2 ^ 32), EaIM), in IV5's zero range (fh_Hp47). *)
assert (IMr : bv_unsigned (ew En1 37) = TFIB_IAL_LO + 8 * (p / 2 ^ 32)).
{ rewrite (HEn1 37%nat ltac:(cbv; zlia)), EaIM. unfold w64. rewrite unsigned_lit_small by (clear - Hp47; numconst; zlia). reflexivity. }
assert (IMb : TFIB_IAL_LO <= TFIB_IAL_LO + 8 * (p / 2 ^ 32) /\ TFIB_IAL_LO + 8 * (p / 2 ^ 32) + 16 <= TFIB_IAL_W) by (clear - Hp47; numconst; zlia).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 37%nat) 8 16 0 0 [YP09.mkChunk 8 (CZero 8)])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem]; rewrite IMr;
split; [clear - IMb; numconst; zlia|]; split; [clear - IMb; numconst; zlia|]; split; [intros o Ho; zlia|];
apply Forall_cons; [|apply Forall_nil]; intros i Hi; cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len YP09.cbyte] in Hi |- *;
exists (Z_to_bv 8 0); split; [reflexivity|]; apply IV5; clear - Hi IMb; numconst; zlia
| apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite IMr, (HEn1 2%nat ltac:(cbv; zlia)), E2; clear - IMb Usp Hlo LB; numconst; unfold sp0 in *; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite IMr, (HEn1 2%nat ltac:(cbv; zlia)), E2; clear - IMb Usp Hlo LB; numconst; unfold sp0 in *; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite IMr; clear - Y5 IMb; numconst; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit TFIB_IAL_LO)) in HS1; [| intros X; discriminate | cbn [sv_denot ms_regs]; symmetry; exact H10r].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
assert (MEQ1 : MEQI mem1).
{ split.
- intros x Hx Hz. rewrite Hfr' by (subst X1; cbn beta; intros [HH|HH]; [apply Hx; left; unfold ASTACK; zlia | exact (Hz HH)]).
apply HF. intros Hw. apply Hx. exact (windows_WIN E0 (ss_mem SS0) _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw).
- exact (conj IV1 (conj IV2 (conj IV3 (conj IV4 IV5)))). }
clear HF HFr Hfr Hfr'.
(* AFga.v:264-276: a1 = p >> 47 = 0 after the step past 0x53e28, a2 = atom 37 at 0x53e3c, then the run to UnwindImpl. *)
srr_run_sh tfibtbl_rtF_ok HS. meq_acc HEn1.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear HS; numconst. pin_zev. rewrite (HEn1 10%nat ltac:(cbv; lia)), E10, Hp10. unfold w64. rewrite unsigned_lit_small by lia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x53e3c. meq_acc HEn1.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 37%nat 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear HS; numconst. pin_zev. rewrite (HEn1 10%nat ltac:(cbv; lia)), (HEn1 37%nat ltac:(cbv; lia)), E10, Hp10, EaIM. unfold w64, TFIB_IAL_LO.
rewrite !unsigned_lit_small by lia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. change (2 ^ 32) with 4294967296 in *.
zcanon_simp. lia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x5bb88. meq_acc HEn1.
(* AFh1.v:209-274: UnwindImpl's premises and its spec U1. *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msU end.
match goal with M : MEQI (ms_mem msU) |- _ => rename M into MEQU end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En1 _ _ HS eq_refl) as Hshape2; cbn [ss_pc] in Hshape2. rewrite Hshape2.
rreg HS (2%bv : bv 5) Q2. rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2 in Q2.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msU) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)).
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; numconst; zlia | off_by ltac:(numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; numconst; zlia | off_by ltac:(numconst; zlia) ]. }
eapply SRr_bind.
{ apply (U1 W ly (ms_regs msU) (ms_mem msU) _ (sp0 - 2128) 0x53f2c sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold sp0. f_equal; zlia. }
1:{ rreg HS (11%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (12%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold sp0. symmetry. apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (14%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity. }
1:{ zlia. }
1:{ memv HS 3%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 7%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 8%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 28%nat 0%nat; [reflexivity | reflexivity | unfold TFIB_TSD; zlia]. }
1:{ memv HS 29%nat 0%nat; [reflexivity | cbn [sv_denot]; rewrite (HEn1 33%nat ltac:(cbv; zlia)), EaC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 30%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 33%nat ltac:(cbv; zlia)), EaC; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 31%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia | reflexivity | zlia]. }
1:{ memv HS 31%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn1 35%nat ltac:(cbv; zlia)), EaTOP; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 31%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn1 35%nat ltac:(cbv; zlia)), EaTOP; unfold w64, ly_bot, kStackSpan; rewrite Zbv_add_unsigned; f_equal; zlia
| unfold ly_bot, kStackSpan; clear - LB; numconst; zlia]. }
1:{ memv HS 32%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); unfold t_unwinding; zlia | reflexivity | zlia]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 32 _ _ HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); numconst; zlia | off_by ltac:(clear - LB; numconst; zlia) ]. }
1:{ memv HS 23%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 24%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia). clear - Hlo LB; numconst; zlia. }
1:{ intros a Ha. rewrite Q2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - Usp Hlo LB; numconst; zlia). apply PRES2. clear - Ha; numconst; zlia. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by zlia.
rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ clear - Hlo LB; numconst; zlia. }
1:{ right. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia). zlia. }
1:{ intros a Ha. apply PRES2. clear - Ha; numconst; zlia. }
1:{ clear; numconst; zlia. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia). zlia. }
1:{ exact Hbot. }
1:{ exact Hhi. }
1:{ apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 2%nat 9%nat;
[cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | cbn [sv_denot]; rewrite (HEn1 1%nat ltac:(cbv; zlia)), E1, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 2%nat 8%nat;
[cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | cbn [sv_denot]; rewrite (HEn1 8%nat ltac:(cbv; zlia)), E8, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ exact Hra4096. }
fold sp0 in Hch. destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hch].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [exact Hch|].
destruct Hch as [H16 Hfp]. split; [exact H16|].
apply Z.ltb_lt in Hf0.
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
eapply fpchain_ext2; [exact Hfp | zlia |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|exact Hva]. intros i Hi. apply aview_same.
apply (proj1 MEQU (Z_to_bv 64 (a + i))); rewrite unsigned_lit_small by (clear - Ha1 Ha2 H16 Hi Usp LB; numconst; zlia).
- apply WIN_not_high. zlia.
- intros Hz. clear - Hz H16 Ha1 Hi LB Hlo. unfold WrapFreeAEnv.IZONE in Hz. numconst. zlia. }
(* AFh1.v:275-335: the unwinder's return; the stack object as lib/AU/WrapMallocBCall.v:403-428 reads it. *)
clear Hle. intros W' c' Hle (-> & regs2 & mem2 & mat2 & -> & HP2 & Hfr2 & Hpr2 & Ht1 & Ht2 & Ht3). srr_norm_model. clear Ht3.
rreg HS (1%bv : bv 5) Q1. rewrite Q1. clear Q1.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem msU x).
{ intros x Hx. rewrite Q2 in Hfr2. unfold w64, BST_SIZE in Hfr2. rewrite unsigned_lit_small in Hfr2 by (clear - Usp Hlo LB; numconst; zlia).
apply Hfr2; clear - Hx; unfold ASTACK, UNW_STK in *; zlia. }
assert (HfrU : forall a, sp0 - 2128 <= a < sp0 - 2120 \/ sp0 - 2116 <= a < sp0 - 2112 -> mem2 (Z_to_bv 64 a) = ms_mem msU (Z_to_bv 64 a)).
{ intros a Ha. rewrite Q2 in Hfr2. unfold w64, BST_SIZE in Hfr2. rewrite unsigned_lit_small in Hfr2 by (clear - Usp Hlo LB; numconst; zlia).
apply Hfr2; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia); clear - Ha; unfold UNW_STK in *; unfold sp0 in *; zlia. }
assert (LEN : (1 <= length tr <= 30)%nat).
{ unfold WrapFreeAEnv.tr, call_trace. destruct (frame0_ok ly regs0); [apply unwind_of_chain_length | cbn; lia]. }
assert (OBJ0 : val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2128) 8 (sp0 - 2112)).
{ eapply val_mem_frame; [intros k Hk; apply HfrU; clear - Hk; zlia|].
memv HS 2%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold w64, sp0; first [f_equal; zlia | rewrite Zbv_add_unsigned; f_equal; zlia]
| clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia]. }
assert (OBJ1 : val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2120) 8 LENv).
{ unfold WrapFreeAEnv.LENv. replace (Z.of_nat (length tr)) with (Z.of_nat (length tr) + 2 ^ 32 * 0) by zlia.
apply val_mem_4_4; [clear - LEN; zlia | zlia | |].
- eapply val_mem_addr; [exact Ht1 | zlia].
- assert (Z8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2120) 8 0)
by (memv HS 2%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | reflexivity | zlia]).
assert (Z4 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2120 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2120 + 4 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by zlia.
rewrite (Z8 (4 + k)%nat ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
eapply val_mem_frame; [intros k Hk; apply HfrU; clear - Hk; zlia | exact Z4]. }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?rim :: ?rscr :: ?rfr :: ?rest =>
pose proof (st_ok_after_call tfibsegs 70 En1 ss ms0 regs2 (mrestrict (w_H W) mem2) (rim :: trim_lo rfr (-64) :: rest) 0x53f88 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_drop; apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP2) as HS1;
let rsv := eval vm_compute in (rim :: trim_lo rfr (-64) :: rest) in
change (rim :: trim_lo rfr (-64) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 70 0x53f88) in
change (ss_after_call ss rsv 70 0x53f88) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs En1 (mrestrict (w_H W) (ms_mem msU)) (mrestrict (w_H W) mem2)) (r0 :: r1 :: tail));
[ constructor; [|constructor];
[ eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite IMr; intros a Ha; cbn beta; clear - Ha Hlo LB Usp IMb; numconst; unfold sp0 in *; zlia
| eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; zlia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts En1 r HEn1 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); intros a Ha; cbn beta; clear - Ha Y1 Y2 Y3 Y4; numconst; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by (intros a Ha; apply Hpr2, PRES2, Ha).
set (En2 := havoc En1 70 (map (getr regs2) CLOB)) in HS1.
assert (HEn2 : forall k, (k < aHAVf)%nat -> ew En2 k = ew E0 k) by (intros k Hk; subst En2; unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; apply HEn1; exact Hk).
assert (IMr2 : bv_unsigned (ew En2 37) = TFIB_IAL_LO + 8 * (p / 2 ^ 32)) by (rewrite (HEn2 37%nat ltac:(cbv; zlia)), <- (HEn1 37%nat ltac:(cbv; zlia)); exact IMr).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold IFRAME;
split; [clear - Usp Hlo LB; numconst; zlia|]; split; [clear - Usp Hlo LB; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; zlia) | apply PRES3; clear - Ho; numconst; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite IMr2, (HEn2 2%nat ltac:(cbv; zlia)), E2; clear - Usp Hlo LB IMb; numconst; unfold sp0 in *; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (MEQ2 : MEQI mem2).
{ destruct MEQU as [M I]. assert (LOWEQ : forall a, a < sp0 - ASTACK -> 0 <= a -> mem2 (Z_to_bv 64 a) = ms_mem msU (Z_to_bv 64 a)).
{ intros a Ha Ha'. apply Hfr'. rewrite unsigned_lit_small by (clear - Ha Ha' Usp; unfold ASTACK in *; zlia). zlia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). apply Hfr'. intros HH. apply Hx. left. unfold ASTACK in *. zlia.
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold WrapFreeAEnv.IAL_POST.
repeat match goal with |- _ /\ _ => split end;
try (eapply val_mem_frame; [|eassumption]; intros k Hk; apply LOWEQ; clear - Hk Hlo LB; numconst; zlia).
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msU) mem2 a) by (apply LOWEQ; clear - Ha Hlo LB; numconst; zlia). apply I5. exact Ha. }
clear MEQU.
(* The run through 0x53f88-0x53f98 and asan_free 0x3189c-0x318c0, stopped at Deallocate's entry 0x318c4 (cf_pc_deallocate). *)
srr_run_to_sh tfibtbl_rtF_ok HS 0x318c4. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En2 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR.
lazymatch type of HF with frame_of _ ?rs _ _ =>
pose proof (MEQI_frame En2 rs _ _ HEn2 ltac:(vm_compute; reflexivity) HF MEQ2) as MEQR end.
assert (FRR : forall y : word, ~ (sp0 - ASTACK <= bv_unsigned y < sp0 - IFRAME) -> ~ (sp0 - 64 <= bv_unsigned y < sp0) ->
~ (T + t_unwinding <= bv_unsigned y < T + t_unwinding + 1) -> ms_mem msR y = mem2 y).
{ intros y Y1 Y2 Y3. apply HF. intros Hw. destruct (in_wrange_windows En2 _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hr;
rewrite ?(HEn2 2%nat ltac:(cbv; zlia)), ?E2, ?(HEn2 32%nat ltac:(cbv; zlia)), ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by (clear - LB; numconst; zlia);
clear - Y1 Y2 Y3 Hr; unfold IFRAME, ASTACK, t_unwinding in *; unfold sp0, T in *; zlia |]).
destruct Hin. }
clear HF.
pose proof stack_ivs as (IT & _).
assert (NT : forall a, sp0 - ASTACK <= a < sp0 -> ~ (T + t_unwinding <= a < T + t_unwinding + 1)).
{ intros a Ha Ht. clear - Ha Ht IT. unfold kThreadObjSize, t_unwinding, ASTACK in *. unfold sp0, T in *. zlia. }
assert (FRM : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ms_mem msR (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
{ intros a Ha. apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia);
[clear - Ha; unfold IFRAME, ASTACK in *; zlia | clear - Ha; zlia | apply NT; clear - Ha; unfold IFRAME, ASTACK in *; zlia]. }
(* at_DEALLOC, as lib/AU/WrapMallocBCall.v:453-507 proves at_ALLOC. *)
apply SRr_ret. unfold at_DEALLOC. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg _ (with_vm_backing _ ?mt _) = _ /\ _ => exists (ms_regs msR), (ms_mem msR), mt end.
split. { rewrite HshR at 1. reflexivity. }
split. { rreg HS (1%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (2%bv : bv 5) R; rewrite R, (HEn2 2%nat ltac:(cbv; zlia)), E2. unfold w64, sp0. f_equal; zlia. }
split. { rreg HS (10%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (11%bv : bv 5) R; rewrite R, (HEn2 10%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (12%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (13%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (14%bv : bv 5) R; rewrite R, (HEn2 2%nat ltac:(cbv; zlia)), E2. unfold w64, sp0. f_equal; zlia. }
split. { rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (3%bv : bv 5) R; rewrite R, (HEn2 3%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
split. { intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
repeat match type of Hr' with _ \/ _ => destruct Hr' as [Hr'|Hr'] end; subst r;
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
let kb := eval vm_compute in (Z_to_bv 5 k : bv 5) in
let RR := fresh "RR" in rreg HS kb RR; change (Z_to_bv 5 k) with kb; rewrite RR, HEn2 by (cbv; zlia); apply Er; reflexivity end. }
split; [exact MEQR|].
split. { memv HS 32%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); unfold t_unwinding; zlia | reflexivity | zlia]. }
split. { intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)); [|destruct (Z_lt_le_dec a (sp0 - 64))].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; clear - Ha l; numconst; unfold sp0; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ].
- apply (apresent_same (w_H W) mem2); [|apply PRES3; exact Ha].
apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia);
[clear - Ha l; numconst; zlia | clear - Ha l0; zlia | exact (NT a Ha)].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; clear - Ha l0; numconst; unfold sp0; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ]. }
split. { eapply val_mem_frame; [|exact OBJ0]. intros k Hk. apply FRM. unfold IFRAME. clear - Hk; zlia. }
split. { eapply val_mem_frame; [|exact OBJ1]. intros k Hk. apply FRM. unfold IFRAME. clear - Hk; zlia. }
split. { intros i Hi. eapply val_mem_addr; [eapply val_mem_frame; [|exact (Ht2 i Hi)] | zlia].
intros k Hk. apply FRM. unfold IFRAME. clear - Hi Hk LEN. zlia. }
split. { memv HS 2%nat 6%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn2 1%nat ltac:(cbv; zlia)), E1, Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 5%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn2 8%nat ltac:(cbv; zlia)), E8, Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 4%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn2 9%nat ltac:(cbv; zlia)), (Er 9 9%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn2 18%nat ltac:(cbv; zlia)), (Er 18 18%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn2 19%nat ltac:(cbv; zlia)), (Er 19 19%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn2 20%nat ltac:(cbv; zlia)), (Er 20 20%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
memv HS 2%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn2 21%nat ltac:(cbv; zlia)), (Er 21 21%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range].
Qed.
End WK.
End c.
