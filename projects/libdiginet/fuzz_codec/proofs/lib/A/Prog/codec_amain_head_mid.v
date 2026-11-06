(* The middle of the HEAD segment of the image-A walk of LLVMFuzzerTestOneInput, between the cuts of
   lib/A/Prog/codec_amain_head_cut.v:
     hm_a: hd_mi (0x80ba0) -> hd_mc (0x84888, the callee's entry): DESK[i] through its instrumented 4-byte check
       (the shadow of row (0x20f40, 12) of CODEC_GLOBS; DESK[2]'s partial granule takes the slow path 0x82af8 and
       back) and the `jal`;
     hm_c: hd_mc2 (0x80bc8, the return) -> hd_mp (0x51e34, the second memset): k.p = s7 = the personality, SPEC_DESK[i]
       through its 8-byte check (row (0x9d660, 24)), k.desk, and the memset's arguments;
     hd_mid: hd_mi -> hd_mp, hm_a, the call of diginet_personality_of through its contract
       (codec_amain_headl.hd_pof_at) and hm_c;
     hd_b (with hm_b): hd_mk (0x80b60) -> hd_mi: kind = op mod 15 stored to k.kind (0x80b94), i = op / 15 mod 3
       in s8 (the multiply-shift forms of codec_amain_heada.v).
   In hm_a and hm_c the desk index i is split into 0, 1, 2 and pinned into s8 as a literal first, so the two table
   addresses and their shadow addresses are literals and the tables are ordinary regions (CPgWalkImg's
   cpg_img_region and cpg_shadow_region). The end cuts are the exit bridge's (codec_amain_st.am_exit, am_mcut). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AD1y.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgEncC CodecRo CodecGlobs CPgWalk CPgWalkImg CPgWalkFrame CPgWalkIntr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem codec_amain_head_cut codec_amain_head_tail codec_amain_headl codec_amain_heada.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition HM_DESK : Z := 0x20f40.
Definition HM_SDESK : Z := 0x9d660.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.

(* a side-stack frame and a table of the image do not meet: the frame's bytes are not the image's *)
Lemma hm_apart : forall B, AR_laws tfibsegs B -> forall ly S W mem md pos lo hi q n,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) -> 0 <= lo < hi -> hi <= 512 -> 0 < n ->
0x10000 <= q -> q + n <= 0x5fb000 ->
frame_addr ly 3 pos + hi <= q \/ q + n <= frame_addr ly 3 pos + lo.
Proof.
intros B LAWS ly S W mem md pos lo hi q n HAR Hin Hlh Hhi Hn Hq Hqn.
set (F := frame_addr ly 3 pos).
destruct (Z_le_gt_dec (F + hi) q) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (q + n) (F + lo)) as [H2|H2]; [right; exact H2|].
exfalso. apply (frm_img tfibsegs B LAWS ly S W mem md 3 pos (Z.max (F + lo) q) HAR Hin).
- change (fs_frame_bytes 3) with 512. fold F. lia.
- apply AD1y.in_img_hull. lia.
Qed.
(* the frame against the image's shadow: the frame lies in one of the two application bands *)
Lemma hm_app_sb : forall F, in_app F 512 -> F + 512 <= SB \/ SB + 2 ^ 44 <= F.
Proof. intros F Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia. Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.

(* mcommon at a segment's end when the walk wrote only the zone Zn, off the cut's kept bytes and shadow *)
Lemma hm_mcommon : forall g pos sp1 c ys ly2 S2 W2 regs2 mem2 md2 k regs3 mem3 md3 k3 pc3 ss3 (Zn : Z -> Prop),
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem3 md3 k3 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
st_ok tfibsegs (am_env g pos c regs2 ys) ss3 (restrict (w_H W2) (mkst regs3 pc3 mem3 (seg_rom tfibsegs))) ->
am_keep_ok (ss_regs ss3) = true ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
(forall a, am_keepzone g pos sp1 a -> ~ Zn a) ->
(forall i, 0 <= i < 56 -> ~ Zn (shadow_addr (FA g pos) + i)) ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs3 mem3 md3.
Proof.
intros g pos sp1 c ys ly2 S2 W2 regs2 mem2 md2 k regs3 mem3 md3 k3 pc3 ss3 Zn HJ Hfr HJ3 HC HS Hkeep KE HZk HZs.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & _).
unfold AM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof HC as HPerm0. do 45 (destruct HPerm0 as (_ & HPerm0)).
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF. split; [apply Z.add_le_mono_l; apply Z.div_le_lower_bound; lia|].
  apply Z.add_le_mono_l. apply Z.div_le_upper_bound; lia. }
unfold SB in Hsh.
eapply (am_exit B MT K XM_LIB LAWS); [exact HC | exact HJ3 | apply env_agree_refl | exact HS | exact Hkeep | | | exact HPerm0].
- intros a Ha. apply KE; [unfold am_keepzone in Ha; lia | exact (HZk a Ha)].
- intros i Hi. rewrite KE; [exact (HSH i Hi) | lia | exact (HZs i Hi)].
Qed.

(* the 8-byte field of a region, read back as the value of its chunk's atom expression *)
Ltac hm_fld HS idx od e v base Ub inl dtac :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth idx (ss_mem ssx) got_region) in
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssx _ idx r HS ltac:(vm_compute; reflexivity)) as HR;
    cbn [ms_mem mkst restrict] in HR;
    lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
      eapply (field_of_region Ev _ n base cs lo hi wlo whi od 8 e v HR Ub);
      [ cbn [In]; inl | dtac | unfold AM_HI in *; try unfold pers_ofA, CA_PERS, CM_SPEC_C24, CM_SPEC_PC; cbn; lia | cbn; lia ] end;
    clear HR end.
(* the same, with the value from the goal and the chunk's expression from the region *)
Ltac hm_find cs od :=
  lazymatch cs with
  | YP09.mkChunk od (CVal _ ?e) :: _ => e
  | _ :: ?t => hm_find t od
  end.
Ltac hm_fld2 HS idx od base Ub dtac :=
  lazymatch goal with |- val_mem _ _ _ 8 ?v =>
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth idx (ss_mem ssx) got_region) in
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssx _ idx r HS ltac:(vm_compute; reflexivity)) as HR;
    cbn [ms_mem mkst restrict] in HR;
    lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
      let e := hm_find cs od in
      eapply (field_of_region Ev _ n base cs lo hi wlo whi od 8 e v HR Ub);
      [ cbn [In]; repeat (first [left; reflexivity | right]) | dtac
      | unfold AM_HI in *; try unfold pers_ofA, CA_PERS, CM_SPEC_C24, CM_SPEC_PC; cbn; lia | cbn; lia ] end;
    clear HR end end.
(* the stopped state's configuration as the cut's *)
Ltac hm_shape W2 pc :=
  lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict _ ?msx) |- _ =>
    let Hpc := fresh "Hpc" in let Hshape := fresh "Hshape" in
    assert (Hpc : ss_pc ssx = pc) by (vm_compute; reflexivity);
    pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) Ev ssx msx HS eq_refl) as Hshape;
    rewrite Hpc in Hshape; rewrite Hshape in HS |- *; clear Hpc Hshape end.
(* a register of the stopped state whose expression is a literal *)
Ltac hm_reg_lit HS r :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    etransitivity; [exact (st_ok_restrict_reg tfibsegs _ Ev ssx _ r HS)|]; vm_compute; reflexivity end.
(* a register of the stopped state that is still its own atom *)
Ltac hm_reg_own HS r HEr :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    etransitivity; [exact (st_ok_restrict_reg tfibsegs _ Ev ssx _ r HS)|];
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e;
    cbn [sv_denot]; rewrite HEr, Z.add_0_r, Z_to_bv_bv_unsigned end.

(* ================================ hd_mi -> hd_mc ================================ *)
Lemma hm_a : forall i g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c kind,
0 <= i <= 2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> 1 <= c -> 0 <= kind <= 14 -> getr regs2 24 = w64 i ->
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176) 4 kind -> hd_kzero g pos 4 W2 mem2 ->
SRr tfibsegs W2 (cfg_at tfibsegs PC_HDI regs2 mem2 md2) (hd_mc B MT K XM_LIB g pos sp1 ops i).
Proof using TL LAWS ML GM ROB.
intros i g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c kind Hi HJ Hfr Hk Hmo HC Hops Hcur Hc1 Hkind H24 V176 HZ4.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold AM_HI in Hchi.
pose proof HC as (Hpre & _ & R2 & _).
destruct Hops as (Hops1 & Hops2).
pose proof Hcur as (Hc & C152 & C160).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF. split; [apply Z.add_le_mono_l; apply Z.div_le_lower_bound; lia|].
  apply Z.add_le_mono_l. apply Z.div_le_upper_bound; lia. }
unfold SB in Hsh.
assert (D1 : HM_DESK / 8 = 16872) by reflexivity.
assert (D2 : (12 + 7) / 8 = 2) by reflexivity.
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c PC_HDI [] [] []
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) I) as HS0.
assert (U2 : bv_unsigned (ew (am_env g pos c regs2 []) 2) = sp1)
  by (rewrite (am_ew_reg g pos c regs2 [] 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (am_env g pos c regs2 []) 32 = Z_to_bv 64 SB) by exact (am_ew_SB g pos c regs2 []).
assert (U32 : bv_unsigned (ew (am_env g pos c regs2 []) 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (HE26 : ew (am_env g pos c regs2 []) 26 = getr regs2 26) by exact (am_ew_reg g pos c regs2 [] 26 26%bv eq_refl).
assert (HTD : forall a, HM_DESK <= a < HM_DESK + 12 ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
  by (intros a Ha; apply (tl_lib_consts B TL); unfold lib_const_addr, HM_DESK in *; lia).
assert (HRO : arodata_okP tfibsegs CA_RLO CA_RHI B (aview tfibsegs (w_H W2) mem2))
  by exact (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 k Hpre HJ).
assert (HG1 : In (HM_DESK, 12) CODEC_GLOBS) by (apply globs_In_b; vm_compute; reflexivity).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 152 <= a < sp1 + 168) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof HJ as HJ0.
unfold cfg_at. change (w64 PC_HDI) with (Z_to_bv 64 PC_HDI).
assert (Hi' : i = 0 \/ i = 1 \/ i = 2) by lia. clear Hi.
destruct Hi' as [-> | [-> | ->]].
all: lazymatch goal with HS0 : st_ok _ ?Ev ?ssx ?msv, H24 : getr _ 24 = w64 ?iv |- _ =>
  pose proof (st_ok_pin_rege Ev ssx msv 24%bv (SLit iv) HS0 ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst]; rewrite H24; reflexivity)) as HS1;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS0 end.
all: ht_keep HS1 [0; 3; 4]%nat.
all: lazymatch goal with HS1 : st_ok _ ?Ev _ _ |- _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (cpg_img_region HM_DESK 12) HS1 eq_refl
    (cpg_img_region_ok B CA_RLO CA_RHI Ev W2 mem2 HM_DESK 12 HRO (am_in_ro HM_DESK 12 eq_refl)
       (fun a Ha => proj1 (HTD a Ha)) (fun a Ha => proj2 (HTD a Ha)) eq_refl ltac:(unfold HM_DESK; lia) ltac:(lia)
       ltac:(unfold HM_DESK; lia))
    ltac:(cbn [ss_mem]; unfold cpg_img_region, HM_DESK; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U2; repeat split; lia)) as HS2;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS1;
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (cpg_shadow_region HM_DESK 12) HS2 eq_refl
    (cpg_shadow_region_ok B Ev W2 mem2 ly2 S2 md2 CODEC_GLOBS HM_DESK 12 GM HG1 HAR E32
       ltac:(unfold HM_DESK; lia) ltac:(unfold HM_DESK; lia))
    ltac:(cbn [ss_mem]; unfold cpg_shadow_region, cpg_img_region; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U2, ?U32, D1, D2; unfold SB, HM_DESK; repeat split; lia)) as HS;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS; clear HS2 end.
(* 0x80ba0 .. jal 0x84888 *)
all: aj_run_to_sh tfibtbl_lib_ok HS HJ AM_pers_of; [ht_awr sp1 U2 | cw_keep ltac:(ht_kwr U2)].
all: hm_shape W2 AM_pers_of; apply SRr_ret; unfold hd_mc.
all: lazymatch goal with HS : st_ok _ _ _ (restrict _ (mkst ?rg3 _ ?m3 _)), HJ3 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  eapply am_mcut; [exact HJ3 | exact Hfr | lia | exact Hmo
  | eapply (hm_mcommon g pos sp1 c [] ly2 S2 W2 regs2 mem2 md2 k rg3 m3 _ k _ _ (fun a => sp1 + 152 <= a < sp1 + 168)
      HJ0 Hfr HJ3 HC HS ltac:(vm_compute; reflexivity) KE);
    [ intros a Ha; unfold am_keepzone in Ha; cbv beta; lia | intros j Hj; cbv beta; lia ]
  | ] end.
all: split; [split; [exact Hops1 | hm_reg_own HS (26%bv : bv 5) HE26; exact Hops2]|].
all: split; [lia|].
all: split; [hm_reg_lit HS (1%bv : bv 5)|]. all: split; [hm_reg_lit HS (10%bv : bv 5)|].
all: split; [hm_reg_lit HS (24%bv : bv 5)|].
all: exists c, kind.
all: split; [split; [exact Hc | split]|].
1, 4, 7: hm_fld HS 4%nat 152 (SOff 35 0) (e_p g + c) sp1 U2 ltac:(left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite (am_ew_CP g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
1, 3, 5: hm_fld HS 4%nat 160 (SOff 36 0) (e_n g - c) sp1 U2 ltac:(right; left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite (am_ew_CN g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
all: split; [exact Hc1|]. all: split; [exact Hkind|].
all: split; [apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2); [|exact V176]; intros x Hx; apply KE; [lia | cbn in Hx; lia]|].
all: intros j Hj; rewrite KE; [exact (HZ4 j Hj) | lia | lia].
Qed.

(* ================================ hd_mc2 -> hd_mp ================================ *)
(* the frame-owning write premise: the record's window at F + 184 .. 200 is the walk's own frame's *)
Ltac hm_awrk sp1 pos U2 U33 EFA :=
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | lazymatch goal with |- awr_ok _ _ _ ?sp0 _ _ _ _ _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ sp0 _ _ _ _ _ 2%nat (sp1 - sp0)) end;
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 3 pos 33%nat);
    [reflexivity | rewrite U33, EFA; reflexivity | left; reflexivity | cbn; lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 3) with 512; lia |] ].
Ltac hm_kwrk U2 U33 :=
  idtac;
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U2, ?U33 in Hb; lia | ]);
  destruct Hr.

Lemma hm_c : forall i g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c kind,
0 <= i <= 2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> 1 <= c -> 0 <= kind <= 14 ->
getr regs2 10 = w64 (pers_ofA CA_PERS i) -> getr regs2 24 = w64 i ->
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176) 4 kind -> hd_kzero g pos 4 W2 mem2 ->
SRr tfibsegs W2 (cfg_at tfibsegs PC_HDP regs2 mem2 md2) (hd_mp B MT K XM_LIB g pos sp1 ops).
Proof using TL LAWS ML GM ROB.
intros i g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c kind Hi HJ Hfr Hk Hmo HC Hops Hcur Hc1 Hkind H10 H24 V176 HZ4.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold AM_HI in Hchi.
pose proof HC as (Hpre & _ & R2 & _).
destruct Hops as (Hops1 & Hops2).
pose proof Hcur as (Hc & C152 & C160).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (FS512 : fs_frame_bytes 3 = 512) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA, FS512 in Happ.
pose proof (hm_app_sb (FA g pos) Happ) as Hsb.
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF. split; [apply Z.add_le_mono_l; apply Z.div_le_lower_bound; lia|].
  apply Z.add_le_mono_l. apply Z.div_le_upper_bound; lia. }
assert (Hfs : FA g pos + 512 <= shadow_addr (FA g pos) \/ shadow_addr (FA g pos) + 64 <= FA g pos).
{ unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. lia. }
unfold SB in Hsh, Hsb.
assert (D1 : HM_SDESK / 8 = 80588) by reflexivity.
assert (D2 : (24 + 7) / 8 = 3) by reflexivity.
pose proof (hm_apart B LAWS ly2 S2 W2 mem2 md2 pos 184 200 HM_SDESK 24 HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold HM_SDESK; lia) ltac:(unfold HM_SDESK; lia)) as Hap.
rewrite EFA in Hap.
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c PC_HDP [] [] []
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) I) as HS0.
assert (U2 : bv_unsigned (ew (am_env g pos c regs2 []) 2) = sp1)
  by (rewrite (am_ew_reg g pos c regs2 [] 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (am_env g pos c regs2 []) 32 = Z_to_bv 64 SB) by exact (am_ew_SB g pos c regs2 []).
assert (U32 : bv_unsigned (ew (am_env g pos c regs2 []) 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew (am_env g pos c regs2 []) 33) = FA g pos)
  by (rewrite (am_ew_F g pos c regs2 []); apply unsigned_lit_small; lia).
assert (HE26 : ew (am_env g pos c regs2 []) 26 = getr regs2 26) by exact (am_ew_reg g pos c regs2 [] 26 26%bv eq_refl).
assert (HE10 : ew (am_env g pos c regs2 []) 10 = getr regs2 10) by exact (am_ew_reg g pos c regs2 [] 10 10%bv eq_refl).
assert (HTS : forall a, HM_SDESK <= a < HM_SDESK + 24 ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
  by (intros a Ha; apply (tl_lib_consts B TL); unfold lib_const_addr, HM_SDESK in *; lia).
assert (HRO : arodata_okP tfibsegs CA_RLO CA_RHI B (aview tfibsegs (w_H W2) mem2))
  by exact (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 k Hpre HJ).
assert (HinRO : forall a, HM_SDESK <= a < HM_SDESK + 24 -> in_roP tfibsegs CA_RLO CA_RHI a)
  by (intros a Ha; right; unfold CA_RLO, CA_RHI, HM_SDESK in *; lia).
assert (HG2 : In (HM_SDESK, 24) CODEC_GLOBS) by (apply globs_In_b; vm_compute; reflexivity).
assert (HRk : region_ok tfibsegs (am_env g pos c regs2 []) (mrestrict (w_H W2) mem2) (am_frame_region 184 200 184 200 []))
  by exact (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c [] 184 200 184 200 []
    HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 184 <= a < FA g pos + 200)) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof HJ as HJ0.
unfold cfg_at. change (w64 PC_HDP) with (Z_to_bv 64 PC_HDP).
assert (Hi' : i = 0 \/ i = 1 \/ i = 2) by lia. clear Hi.
destruct Hi' as [-> | [-> | ->]].
all: lazymatch goal with HS0 : st_ok _ ?Ev ?ssx ?msv, H24 : getr _ 24 = w64 ?iv |- _ =>
  pose proof (st_ok_pin_rege Ev ssx msv 24%bv (SLit iv) HS0 ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst]; rewrite H24; reflexivity)) as HS1;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS0 end.
all: ht_keep HS1 [0; 3; 4]%nat.
all: lazymatch goal with HS1 : st_ok _ ?Ev _ _ |- _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (am_frame_region 184 200 184 200 []) HS1 eq_refl HRk
    ltac:(cbn [ss_mem]; unfold am_frame_region; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U33, U2; repeat split; lia)) as HS2;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS1;
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (cpg_img_region HM_SDESK 24) HS2 eq_refl
    (cpg_img_region_ok B CA_RLO CA_RHI Ev W2 mem2 HM_SDESK 24 HRO HinRO
       (fun a Ha => proj1 (HTS a Ha)) (fun a Ha => proj2 (HTS a Ha)) eq_refl ltac:(unfold HM_SDESK; lia) ltac:(lia)
       ltac:(unfold HM_SDESK; lia))
    ltac:(cbn [ss_mem]; unfold cpg_img_region, am_frame_region; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U2, ?U33; unfold HM_SDESK in *; repeat split; lia)) as HS3;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3; clear HS2;
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (cpg_shadow_region HM_SDESK 24) HS3 eq_refl
    (cpg_shadow_region_ok B Ev W2 mem2 ly2 S2 md2 CODEC_GLOBS HM_SDESK 24 GM HG2 HAR E32
       ltac:(unfold HM_SDESK; lia) ltac:(unfold HM_SDESK; lia))
    ltac:(cbn [ss_mem]; unfold cpg_shadow_region, cpg_img_region, am_frame_region; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U2, ?U32, ?U33, D1, D2; unfold SB, HM_SDESK;
          repeat split; lia)) as HS;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS; clear HS3 end.
(* 0x80bc8 .. jal 0x51e34 *)
all: aj_run_to_sh tfibtbl_lib_ok HS HJ CA_MEMSET; [hm_awrk sp1 pos U2 U33 EFA | cw_keep ltac:(hm_kwrk U2 U33)].
all: hm_shape W2 CA_MEMSET; apply SRr_ret; unfold hd_mp.
all: lazymatch goal with HS : st_ok _ _ _ (restrict _ (mkst ?rg3 _ ?m3 _)), HJ3 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  eapply am_mcut; [exact HJ3 | exact Hfr | lia | exact Hmo
  | eapply (hm_mcommon g pos sp1 c [] ly2 S2 W2 regs2 mem2 md2 k rg3 m3 _ k _ _
      (fun a => (sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 184 <= a < FA g pos + 200))
      HJ0 Hfr HJ3 HC HS ltac:(vm_compute; reflexivity) KE);
    [ intros a Ha; unfold am_keepzone in Ha; cbv beta; lia | intros j Hj; cbv beta; lia ]
  | ] end.
all: split; [split; [exact Hops1 | hm_reg_own HS (26%bv : bv 5) HE26; exact Hops2]|].
all: split; [hm_reg_lit HS (1%bv : bv 5)|].
all: split; [lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
  etransitivity; [exact (st_ok_restrict_reg tfibsegs _ Ev ssx _ (10%bv : bv 5) HS)|];
  let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in change (sr_get (ss_regs ssx) (10%bv : bv 5)) with e;
  rewrite (am_den_off _ 33%nat (FA g pos) 252 (am_ew_F g pos c regs2 []) ltac:(lia) ltac:(lia)); reflexivity end|].
all: split; [hm_reg_lit HS (11%bv : bv 5)|]. all: split; [hm_reg_lit HS (12%bv : bv 5)|].
(* the three desks: NULL, Control|24, ProControl *)
1: exists c, kind, (pers_ofA CA_PERS 0), 0, None.
2: exists c, kind, (pers_ofA CA_PERS 1), CM_SPEC_C24, (Some DgnSpec.c24).
3: exists c, kind, (pers_ofA CA_PERS 2), CM_SPEC_PC, (Some DgnSpec.pc).
all: split; [split; [exact Hc | split]|].
1, 4, 7: hm_fld HS 5%nat 152 (SOff 35 0) (e_p g + c) sp1 U2 ltac:(repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (am_ew_CP g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
1, 3, 5: hm_fld HS 5%nat 160 (SOff 36 0) (e_n g - c) sp1 U2 ltac:(repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (am_ew_CN g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
all: split; [exact Hc1|]. all: split; [exact Hkind|].
all: split; [unfold pd_okA, pers_ofA, CA_PERS, CM_SPEC_C24, CM_SPEC_PC; cbn;
  first [solve [left; repeat split] | solve [right; left; repeat split] | solve [right; right; repeat split]]|].
all: split; [hm_reg_own HS (23%bv : bv 5) HE10; exact H10|].
all: split; [apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2); [|exact V176]; intros x Hx; apply KE; [lia | cbn in Hx; cbv beta; lia]|].
all: split; [hm_fld2 HS 2%nat 184 (FA g pos) U33
  ltac:(cbn [sv_denot]; rewrite HE10, Z.add_0_r, Z_to_bv_bv_unsigned; exact H10)|].
all: split; [hm_fld2 HS 2%nat 192 (FA g pos) U33 ltac:(cbn [sv_denot]; reflexivity)|].
all: split; [intros j Hj; rewrite KE; [apply HZ4; lia | lia | cbv beta; lia]|].
all: intros j Hj; rewrite KE; [apply HZ4; lia | lia | cbv beta; lia].
Qed.

(* ================================ hd_mi -> hd_mp, through the call ================================ *)
Hypothesis MTL : ameter_laws MT.
Hypothesis POF : cdc_pers_of_specX tfibsegs B MT AM_pers_of CA_PERS.
Lemma hd_mid : forall g pos sp1 ops W2 c2, hd_mi B MT K XM_LIB g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (hd_mp B MT K XM_LIB g pos sp1 ops).
Proof using TL LAWS ML GM ROB MTL POF.
intros g pos sp1 ops W2 c2
  (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops &
   (c & kind & i & Hcur & Hc1 & Hkind & Hi & H24 & V176 & HZ4)).
eapply SRr_bind;
  [exact (hm_a i g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c kind Hi HJ Hfr Hk Hmo HC Hops Hcur Hc1 Hkind H24 V176 HZ4)|].
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & k3 & -> & HJ3 & Hfr3 & Hk3 & Hmo3 & HC3 &
  (Hops3 & Hi3 & H1 & H10 & H243 & (c' & kind' & Hcur3 & Hc13 & Hkind3 & V1763 & HZ43))).
assert (Ek : k3 = 0) by (unfold EV_LIB in Hk3; lia). subst k3.
apply (hd_pof_at B MT K XM_LIB MTL LAWS POF (hd_mp B MT K XM_LIB g pos sp1 ops) g pos sp1 0 ly3 S3 W3 regs3 mem3 md3
  c' i PC_HDP HJ3 Hfr3 Hmo3 HC3 Hcur3 H10 ltac:(lia) H1 ltac:(apply ret_ok_even; vm_compute; reflexivity)
  ltac:(unfold PC_HDP; lia)).
intros W4 ly4 S4 regs4 mem4 md4 HJ4 Hfr4 Hmo4 HC4 Hcur4 HPR4 H104 KF.
assert (P26 : getr regs4 26 = getr regs3 26) by exact (HPR4 26 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs4 24 = getr regs3 24) by exact (HPR4 24 ltac:(unfold acallee_saved; lia)).
destruct Hops3 as (Hops31 & Hops32).
apply (hm_c i g pos sp1 ops ly4 S4 W4 regs4 mem4 md4 0 c' kind' Hi3 HJ4 Hfr4 ltac:(unfold EV_LIB; lia) Hmo4 HC4
  (conj Hops31 (eq_trans P26 Hops32)) Hcur4 Hc13 Hkind3 H104 (eq_trans P24 H243)).
- apply (cw_val_mem_kept (w_H W3) (w_H W4) mem3 mem4); [|exact V1763].
  intros x Hx. apply KF. cbn in Hx. lia.
- intros j Hj. rewrite KF by lia. exact (HZ43 j Hj).
Qed.

(* ================================ hd_mk -> hd_mi ================================ *)
(* 0x80b60-0x80b9c: kind = op mod 15 stored to k.kind (0x80b94), i = op / 15 mod 3 in s8 (codec_amain_heada.v) *)
Lemma hm_b : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c op,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> 1 <= c -> 0 <= op < 256 -> getr regs2 23 = w64 op ->
hd_kzero g pos 0 W2 mem2 ->
SRr tfibsegs W2 (cfg_at tfibsegs PC_HDK regs2 mem2 md2) (hd_mi B MT K XM_LIB g pos sp1 ops).
Proof using TL LAWS ML.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c op HJ Hfr Hk Hmo HC Hops Hcur Hc1 Hop H23 HZ0.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold AM_HI in Hchi.
pose proof HC as (Hpre & _ & R2 & _).
destruct Hops as (Hops1 & Hops2).
pose proof Hcur as (Hc & C152 & C160).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (FS512 : fs_frame_bytes 3 = 512) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA, FS512 in Happ.
pose proof (hm_app_sb (FA g pos) Happ) as Hsb.
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF. split; [apply Z.add_le_mono_l; apply Z.div_le_lower_bound; lia|].
  apply Z.add_le_mono_l. apply Z.div_le_upper_bound; lia. }
assert (Hfs : FA g pos + 512 <= shadow_addr (FA g pos) \/ shadow_addr (FA g pos) + 64 <= FA g pos).
{ unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. lia. }
unfold SB in Hsh, Hsb.
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c PC_HDK [] [] []
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) I) as HS0.
assert (U2 : bv_unsigned (ew (am_env g pos c regs2 []) 2) = sp1)
  by (rewrite (am_ew_reg g pos c regs2 [] 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (am_env g pos c regs2 []) 33) = FA g pos)
  by (rewrite (am_ew_F g pos c regs2 []); apply unsigned_lit_small; lia).
assert (HE26 : ew (am_env g pos c regs2 []) 26 = getr regs2 26) by exact (am_ew_reg g pos c regs2 [] 26 26%bv eq_refl).
assert (U23 : bv_unsigned (ew (am_env g pos c regs2 []) 23) = op)
  by (rewrite (am_ew_reg g pos c regs2 [] 23 23%bv eq_refl), H23; unfold w64; apply unsigned_lit_small; lia).
assert (UK : U (am_env g pos c regs2 []) hd_kind_e = op mod 15) by (rewrite hd_kind_val; rewrite U23; lia).
assert (UI : U (am_env g pos c regs2 []) hd_i_e = op / 15 mod 3) by (rewrite hd_i_val; rewrite U23; lia).
pose proof (Z.mod_pos_bound op 15 ltac:(lia)) as MK.
pose proof (Z.mod_pos_bound (op / 15) 3 ltac:(lia)) as MI.
assert (HRk : region_ok tfibsegs (am_env g pos c regs2 []) (mrestrict (w_H W2) mem2) (am_frame_region 176 180 176 180 []))
  by exact (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c [] 176 180 176 180 []
    HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 176 <= a < FA g pos + 180)) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof HJ as HJ0.
unfold cfg_at. change (w64 PC_HDK) with (Z_to_bv 64 PC_HDK).
ht_keep HS0 [0; 3; 4]%nat.
lazymatch goal with HS0 : st_ok _ ?Ev _ _ |- _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (am_frame_region 176 180 176 180 []) HS0 eq_refl HRk
    ltac:(cbn [ss_mem]; unfold am_frame_region; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U33, U2; repeat split; lia)) as HS;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS; clear HS0 end.
(* 0x80b60 .. 0x80ba0 *)
aj_run_to_sh tfibtbl_lib_ok HS HJ PC_HDI; [hm_awrk sp1 pos U2 U33 EFA | cw_keep ltac:(hm_kwrk U2 U33)].
hm_shape W2 PC_HDI; apply SRr_ret; unfold hd_mi.
lazymatch goal with HS : st_ok _ _ _ (restrict _ (mkst ?rg3 _ ?m3 _)), HJ3 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  eapply am_mcut; [exact HJ3 | exact Hfr | lia | exact Hmo
  | eapply (hm_mcommon g pos sp1 c [] ly2 S2 W2 regs2 mem2 md2 k rg3 m3 _ k _ _
      (fun a => (sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 176 <= a < FA g pos + 180))
      HJ0 Hfr HJ3 HC HS ltac:(vm_compute; reflexivity) KE);
    [ intros a Ha; unfold am_keepzone in Ha; cbv beta; lia | intros j Hj; cbv beta; lia ]
  | ] end.
split; [split; [exact Hops1 | hm_reg_own HS (26%bv : bv 5) HE26; exact Hops2]|].
exists c, (op mod 15), (op / 15 mod 3).
split; [split; [exact Hc | split]|].
1: hm_fld HS 3%nat 152 (SOff 35 0) (e_p g + c) sp1 U2 ltac:(repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (am_ew_CP g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
1: hm_fld HS 3%nat 160 (SOff 36 0) (e_n g - c) sp1 U2 ltac:(repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (am_ew_CN g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
split; [exact Hc1|]. split; [lia|]. split; [lia|].
split.
{ lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    etransitivity; [exact (st_ok_restrict_reg tfibsegs _ Ev ssx _ (24%bv : bv 5) HS)|];
    change (sr_get (ss_regs ssx) (24%bv : bv 5)) with hd_i_e end.
  unfold w64. rewrite <- UI. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssx _ 0 r HS ltac:(vm_compute; reflexivity)) as HR;
    cbn [ms_mem mkst restrict] in HR;
    lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
      let e := hm_find cs 176 in
      pose proof (field_of_region_any Ev _ n (FA g pos) cs lo hi wlo whi 176 4 e HR U33
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as VK;
      change (bv_unsigned (sv_denot Ev e)) with (U Ev hd_kind_e) in VK end end.
  rewrite UK, (Z.mod_small (op mod 15)) in VK by (cbn; lia).
  exact VK. }
intros j Hj. rewrite KE; [apply HZ0; lia | lia | cbv beta; lia].
Qed.

Lemma hd_b : forall g pos sp1 ops W2 c2, hd_mk B MT K XM_LIB g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (hd_mi B MT K XM_LIB g pos sp1 ops).
Proof using TL LAWS ML.
intros g pos sp1 ops W2 c2
  (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & (c & op & Hcur & Hc1 & Hop & H23 & HZ0)).
exact (hm_b g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c op HJ Hfr Hk Hmo HC Hops Hcur Hc1 Hop H23 HZ0).
Qed.
End b.
End a.
