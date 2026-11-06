(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths and module names changed; 461 of its 500 lines of code are new or changed and 184 lines of the source are left out. *)
(* The HEAD segment of the image-A walk of LLVMFuzzerTestOneInput, 0x80abc-0x80c30 (lib/A/Prog/codec_amain_inv.v
   seg_head), in parts, each from one cut of lib/A/Prog/codec_amain_head_cut.v to the next:
   - hd_a1: 0x80abc ld in.n and the test (0x80ac0): in.n = 0 leaves the loop at EXIT 0x82f94; else the cursor
     advances (0x80ac8-0x80ad8), the instrumented check of the op byte at e_p + c passes (0x80adc-0x80aec, its
     slow path at 0x82aec) and the byte is read into s7 (0x80af0);
   - hd_a2: 0x80af4-0x80b5c, k's 23 shadow bytes set to 0 (k marked usable) and the call of the checked memset
     of the record;
   - hd_memset1: that call, by the runtime's contract;
   - hd_b: 0x80b60-0x80b9c, the kind written to k (0x80b94) and the desk index in s8;
   - hd_memset2: the call of the checked memset of before and out (0x80c08), which leaves the record k_rdZ. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgEncC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkImg CPgWalkIntr CPgWalkKept CPgWalkFrame CPgWalkCall CPgTokJ.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_encl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_rdin codec_amain_head_cut codec_amain_heada codec_amain_headl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_head_mid codec_amain_head_tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x80af4, the op byte read: the cut between the token run of the instrumented check and the shadow stores *)
Definition PC_HDB : Z := 0x80af4.
Definition hd_shr : smem := [am_shadow_region 22 45 am_shm8].

(* a range of the image, by computation over the loaded segments *)
Definition hd_img_b (q n : Z) : bool :=
existsb (fun sg => (Z.of_N (seg_base sg) <=? q) && (q + n <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool tfibsegs.
Lemma hd_in_img_of : forall q n a, hd_img_b q n = true -> q <= a < q + n -> in_img tfibsegs a.
Proof.
intros q n a Hb Ha. unfold hd_img_b in Hb. apply existsb_exists in Hb as (sg & Hin & Hc).
apply andb_prop in Hc as (Hlo & Hhi). apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
exists sg. split; [exact Hin | lia].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet CA_MEMSET.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis POF : cdc_pers_of_specX tfibsegs B MT AM_pers_of CA_PERS.

Definition hd_mb (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut B MT K XM_LIB g pos sp1 SH_F8 PC_HDB (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c op, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ 0 <= op < 256 /\ getr regs2 23 = w64 op).

(* the frame, its shadow and the machine stack do not meet *)
Ltac hd_sep := unfold shadow_addr, SHADOW_OFF, SB in *; lia.

(* the write windows of the base state: the cursor only *)
Ltac hd_awr sp1v U2 :=
idtac; lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own) end;
lazymatch goal with |- awr_ok _ _ _ ?sp0 _ _ _ _ _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ sp0 _ _ _ _ _ 2%nat (sp1v - sp0));
  [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U2; lia
  | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ] end.
(* the same with the frame's shadow window (the 23 stores of k's shadow bytes) *)
Ltac hd_awr_s sp1v U2 U34 EFA posv :=
idtac; lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own) end;
lazymatch goal with |- awr_ok _ _ _ ?sp0 _ _ _ _ _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ sp0 _ _ _ _ _ 2%nat (sp1v - sp0));
  [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U2; lia
  | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 posv 34%nat);
  [reflexivity | rewrite EFA; rewrite ?ew_ewset_other by lia; rewrite U34; reflexivity | left; reflexivity
  | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (fs_frame_bytes 3 / 8) with 64; lia |] ] end.
(* the zone of those windows: the cursor and k's 23 shadow bytes *)
Ltac hd_kwr_s U2 U34 :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
    rewrite ?U2, ?U34 in Hb; first [left; lia | right; lia | lia] | ]);
destruct Hr.
(* the zone of those windows: the cursor only *)
Ltac hd_kwr U2 :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
    rewrite ?U2 in Hb; lia | ]);
destruct Hr.
(* the stopped state as the configuration of a cut *)
Ltac hd_shape W2 HS pc :=
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let Hpc := fresh "Hpc" in let Hshape := fresh "Hshape" in
  assert (Hpc : ss_pc ssx = pc) by (vm_compute; reflexivity);
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) _ ssx msx HS eq_refl) as Hshape;
  rewrite Hpc in Hshape; rewrite Hshape in HS |- *; clear Hpc Hshape end.
(* one 8-byte field of the cursor, at offset od of the window, as the atom at_ plus k *)
Ltac hd_cur W2 HS sp1v U2 od at_ kk v ewl inl :=
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
  let HR := fresh "HR" in
  pose proof (st_ok_region_nth Ev ssx (restrict (w_H W2) msx) 4 r HS ltac:(vm_compute; reflexivity)) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    apply (field_of_region Ev (mrestrict (w_H W2) (ms_mem msx)) n sp1v cs lo hi wlo whi od 8 (SOff at_ kk) v HR);
    [ rewrite ?ew_ewset_other by lia; rewrite U2; reflexivity
    | cbn [In]; inl
    | rewrite (am_den_off Ev at_ _ kk ltac:(rewrite ?ew_ewset_other by lia; exact ewl))
        by (unfold AM_HI in *; lia); f_equal; lia
    | unfold AM_HI in *; cbn; lia
    | cbn; lia ] end end.

Lemma hd_a1 : forall g pos sp1 ops W2 c2, inv_head B MT K XM_LIB g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => inv_exit B MT K XM_LIB g pos sp1 W3 c3 \/ hd_mb g pos sp1 ops W3 c3).
Proof using TL LAWS ML.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & (c & Hcur)).
assert (Ek : k = 0) by (unfold EV_LIB in Hk; lia). subst k.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold AM_HI in Hchi, Hpng.
destruct Hops as (Hops1 & Hops2). pose proof Hcur as (Hc & C152 & C160).
pose proof HC as HPerm0. do 45 (destruct HPerm0 as (_ & HPerm0)).
pose proof HC as HSHC. do 43 (destruct HSHC as (_ & HSHC)). destruct HSHC as (HSHC & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HJ as (HAR & _).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA in Happ. change (fs_frame_bytes 3) with 512 in Happ.
assert (D2 : 512 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia).
assert (D1 : FA g pos / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
assert (D3 : 8 * (FA g pos / 8) <= FA g pos) by (apply Z.mul_div_le; lia).
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44)
  by (unfold shadow_addr, SHADOW_OFF, SB; lia).
pose proof (rd_ib_range g c) as Hopr.
set (op := rd_ib g c) in *.
assert (HE33 : ew (am_env g pos c regs2 [op]) 33 = Z_to_bv 64 (FA g pos)) by exact (am_ew_F g pos c regs2 [op]).
assert (HE34 : ew (am_env g pos c regs2 [op]) 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by exact (am_ew_SH g pos c regs2 [op]).
assert (HE35 : ew (am_env g pos c regs2 [op]) 35 = Z_to_bv 64 (e_p g + c)) by exact (am_ew_CP g pos c regs2 [op]).
assert (HE36 : ew (am_env g pos c regs2 [op]) 36 = Z_to_bv 64 (e_n g - c)) by exact (am_ew_CN g pos c regs2 [op]).
assert (HE32 : ew (am_env g pos c regs2 [op]) 32 = Z_to_bv 64 SB) by exact (am_ew_SB g pos c regs2 [op]).
assert (HE37 : ew (am_env g pos c regs2 [op]) 37 = Z_to_bv 64 op).
{ change 37%nat with (AM_X0 + 0)%nat. rewrite (am_ew_y g pos c regs2 [op] 0). reflexivity. }
assert (HE2 : ew (am_env g pos c regs2 [op]) 2 = getr regs2 2) by exact (am_ew_reg g pos c regs2 [op] 2 2%bv eq_refl).
assert (HE26 : ew (am_env g pos c regs2 [op]) 26 = Z_to_bv 64 ops)
  by (rewrite (am_ew_reg g pos c regs2 [op] 26 26%bv eq_refl), Hops2; reflexivity).
assert (U2 : bv_unsigned (ew (am_env g pos c regs2 [op]) 2) = sp1)
  by (rewrite HE2; pose proof HC as (_ & _ & R2 & _); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (am_env g pos c regs2 [op]) 34) = shadow_addr (FA g pos))
  by (rewrite HE34; apply unsigned_lit_small; unfold SB in Hsh; lia).
assert (U35 : bv_unsigned (ew (am_env g pos c regs2 [op]) 35) = e_p g + c)
  by (rewrite HE35; apply unsigned_lit_small; lia).
pose proof HJ as HJR.
assert (HAE0 : env_agree 35 (am_env g pos c regs2 [op]) (am_env g pos c regs2 [op])) by apply env_agree_refl.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 152 <= a < sp1 + 168) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
destruct (Z.eq_dec c (e_n g)) as [Hce | Hcne].
- (* in.n = 0: the jump to EXIT *)
  pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 0 c PC_HEAD [op] [] []
    HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) (Forall_nil _) ltac:(cbn; exact I) (Forall_nil _) I) as HS.
  assert (SHOK : sh_ok tfibsegs CW_Bx [] (am_env g pos c regs2 [op]) (mrestrict (w_H W2) mem2)) by constructor.
  unfold cfg_at. change (w64 PC_HEAD) with (Z_to_bv 64 PC_HEAD).
  aj_run_sh tfibtbl_lib_ok HS HJR. { hd_awr sp1 U2. }
  cw_keep ltac:(hd_kwr U2).
  srr_branch_sh tfibtbl_lib_ok HS.
  all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hcond end.
  all: rewrite branch_ne_U in Hcond.
  all: rewrite (cw_U_atom0 _ 36%nat (e_n g - c) ltac:(rewrite ?ew_ewset_other by lia; exact HE36) ltac:(lia)) in Hcond.
  all: rewrite U_lit in Hcond by lia.
  + exfalso. apply negb_true_iff, Z.eqb_neq in Hcond. lia.
  + aj_run_to_sh tfibtbl_lib_ok HS HJR PC_EXIT. { hd_awr sp1 U2. }
    cw_keep ltac:(hd_kwr U2).
    hd_shape W2 HS PC_EXIT.
    apply SRr_ret. left. unfold inv_exit.
    eapply am_mcut; [exact HJR | exact Hfr | lia | exact Hmo | | exact I].
    eapply (am_exit B MT K XM_LIB LAWS);
    [ exact HC | exact HJR | idtac | exact HS | vm_compute; reflexivity
    | intros a Ha; unfold am_keepzone in Ha; apply KE; [unfold SB in *; lia | lia]
    | intros i Hi; rewrite (KE (shadow_addr (FA g pos) + i) ltac:(unfold shadow_addr, SHADOW_OFF, SB in *; lia)
        ltac:(unfold shadow_addr, SHADOW_OFF, SB in *; lia)); exact (HSHC i Hi)
    | exact HPerm0 ].
    env_agree_chain HAE0.
- (* in.n <> 0: the op byte at e_p + c *)
  assert (Hcn : c < e_n g) by lia.
  assert (HRS : Forall (region_ok tfibsegs (am_env g pos c regs2 [op]) (mrestrict (w_H W2) mem2)) [rd_inr 0]).
  { constructor; [|constructor].
    eapply (rd_inr_ok B MT K XM_LIB LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 0 mem2 md2 0 c 0%nat
      (am_env g pos c regs2 [op]) HJ Hfr HC HJ ltac:(lia) ltac:(cbn; lia) HE35).
    unfold AM_X0. cbn [Nat.add]. rewrite Z.add_0_r. exact HE37. }
  pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC ltac:(lia))
    as (HSEP1 & HSEP2).
  destruct (Hblk ltac:(lia)) as (Hin2 & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
  assert (HNI : forall a, e_p g <= a < e_p g + req_size (e_n g) -> in_img tfibsegs a -> False).
  { intros a Ha Him. apply (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR); [|exact Him].
    left. exists (e_p g), (e_n g). split; [exact Hin2 | exact Ha]. }
  assert (HGOT : e_p g + c + 1 <= 645904 \/ 645912 <= e_p g + c).
  { destruct (Z_le_gt_dec (e_p g + c + 1) 645904) as [HH|HH]; [left; exact HH|].
    destruct (Z_le_gt_dec 645912 (e_p g + c)) as [HH2|HH2]; [right; exact HH2|].
    exfalso. apply (HNI (e_p g + c)); [lia|].
    apply (hd_in_img_of 645904 8 (e_p g + c) ltac:(vm_compute; reflexivity)). lia. }
  assert (HBC : e_p g + c + 1 <= 681080 \/ 681088 <= e_p g + c).
  { destruct (Z_le_gt_dec (e_p g + c + 1) 681080) as [HH|HH]; [left; exact HH|].
    destruct (Z_le_gt_dec 681088 (e_p g + c)) as [HH2|HH2]; [right; exact HH2|].
    exfalso. apply (HNI (e_p g + c)); [lia|].
    apply (hd_in_img_of 681080 8 (e_p g + c) ltac:(vm_compute; reflexivity)). lia. }
  assert (HAP : Forall (fun r => all_disjoint (am_env g pos c regs2 [op]) r am_regs) [rd_inr 0]).
  { constructor; [|constructor].
    unfold am_regs, am_regs0, cw_regs, rd_inr, am_spill_region, am_cur_region, stack_region, got_region, bcell_region.
    cbn [app all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_nat]. rewrite U2, U35.
    unfold A_GOT_shadow, A_shadow_glob in *. repeat split; lia. }
  pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 0 c PC_HEAD [op]
    [rd_inr 0] [] HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) HRS ltac:(cbn; repeat split; exact I) HAP I) as HS.
  assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 35 0 1] (am_env g pos c regs2 [op]) (mrestrict (w_H W2) mem2)).
  { constructor; [|constructor].
    exact (am_cur_shent B MT K XM_LIB LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 0 c [op] 1
             HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia)). }
  unfold cfg_at. change (w64 PC_HEAD) with (Z_to_bv 64 PC_HEAD).
  cwj_run ltac:(hd_awr sp1 U2).
  cw_keep ltac:(hd_kwr U2).
  cw_branch Hcond.
  all: rewrite branch_ne_U in Hcond.
  all: rewrite (cw_U_atom0 _ 36%nat (e_n g - c) ltac:(rewrite ?ew_ewset_other by lia; exact HE36) ltac:(lia)) in Hcond.
  all: rewrite U_lit in Hcond by lia.
  + (* taken: the cursor advance, the instrumented check and the byte *)
    cwj_run_to ltac:(hd_awr sp1 U2) PC_HDB.
    cw_keep ltac:(hd_kwr U2).
    hd_shape W2 HS PC_HDB.
    apply SRr_ret. right. unfold hd_mb.
    eapply am_mcut; [exact HJR | exact Hfr | lia | exact Hmo | |].
    * eapply (am_exit B MT K XM_LIB LAWS);
      [ exact HC | exact HJR | idtac | exact HS | vm_compute; reflexivity
      | intros a Ha; unfold am_keepzone in Ha; apply KE; [unfold SB in *; lia | lia]
      | intros i Hi; rewrite (KE (shadow_addr (FA g pos) + i) ltac:(unfold shadow_addr, SHADOW_OFF, SB in *; lia)
          ltac:(unfold shadow_addr, SHADOW_OFF, SB in *; lia)); exact (HSHC i Hi)
      | exact HPerm0 ].
      env_agree_chain HAE0.
    * split.
      -- split; [lia|].
         lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
           rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx (26%bv : bv 5) HS) end.
         change (sr_get (ss_regs _) (26%bv : bv 5)) with (SOff 26 0).
         cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite HE26, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- exists (c + 1), op. split; [|split; [lia | split; [exact Hopr|]]].
         ++ unfold cur_at. split; [lia|]. split.
            ** hd_cur W2 HS sp1 U2 152 35%nat 1 (e_p g + (c + 1)) HE35 ltac:(right; left; reflexivity).
            ** hd_cur W2 HS sp1 U2 160 36%nat (-1) (e_n g - (c + 1)) HE36 ltac:(left; reflexivity).
         ++ lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
              rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx (23%bv : bv 5) HS) end.
            change (sr_get (ss_regs _) (23%bv : bv 5)) with (SExt false 8 (SOff 37 0)).
            rewrite denot_lit_U, U_SExt. cbv iota beta.
            lazymatch goal with |- context [U ?Ev (SOff 37 0)] =>
              rewrite (cw_U_atom0 Ev 37%nat op ltac:(rewrite ?ew_ewset_other by lia; exact HE37) ltac:(lia)) end.
            change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small op 256) by lia.
            rewrite zcanon_id by (unfold M64; lia). reflexivity.
  + exfalso. apply negb_false_iff, Z.eqb_eq in Hcond. lia.
Qed.

(* ---- 0x80af4-0x80b5c: k's 23 shadow bytes, then the call of the checked memset of the record ---- *)
Lemma hd_a2 : forall g pos sp1 ops W2 c2, hd_mb g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (hd_ms1 B MT K XM_LIB g pos sp1 ops).
Proof using TL LAWS ML.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & (c & op & Hcur & Hc1 & Hopr & H23)).
assert (Ek : k = 0) by (unfold EV_LIB in Hk; lia). subst k.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold AM_HI in Hchi, Hpng.
destruct Hops as (Hops1 & Hops2). pose proof Hcur as (Hc & C152 & C160).
pose proof HC as HPerm0. do 45 (destruct HPerm0 as (_ & HPerm0)).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HJ as (HAR & _).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA in Happ. change (fs_frame_bytes 3) with 512 in Happ.
assert (D2 : 512 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia).
assert (D1 : FA g pos / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
assert (D3 : 8 * (FA g pos / 8) <= FA g pos) by (apply Z.mul_div_le; lia).
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44)
  by (unfold shadow_addr, SHADOW_OFF, SB; lia).
assert (Hfsh : FA g pos + 512 <= shadow_addr (FA g pos) \/ shadow_addr (FA g pos) + 64 <= FA g pos).
{ unfold in_app in Happ. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  destruct Happ as (_ & [Hlow | (Hh1 & Hh2)]); [left; lia|].
  right. assert (D4 : 2199291686912 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (HE33 : ew (am_env g pos c regs2 []) 33 = Z_to_bv 64 (FA g pos)) by exact (am_ew_F g pos c regs2 []).
assert (HE34 : ew (am_env g pos c regs2 []) 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by exact (am_ew_SH g pos c regs2 []).
assert (HE35 : ew (am_env g pos c regs2 []) 35 = Z_to_bv 64 (e_p g + c)) by exact (am_ew_CP g pos c regs2 []).
assert (HE36 : ew (am_env g pos c regs2 []) 36 = Z_to_bv 64 (e_n g - c)) by exact (am_ew_CN g pos c regs2 []).
assert (HE2 : ew (am_env g pos c regs2 []) 2 = getr regs2 2) by exact (am_ew_reg g pos c regs2 [] 2 2%bv eq_refl).
assert (HE26 : ew (am_env g pos c regs2 []) 26 = Z_to_bv 64 ops)
  by (rewrite (am_ew_reg g pos c regs2 [] 26 26%bv eq_refl), Hops2; reflexivity).
assert (HE23 : ew (am_env g pos c regs2 []) 23 = Z_to_bv 64 op)
  by (rewrite (am_ew_reg g pos c regs2 [] 23 23%bv eq_refl), H23; reflexivity).
assert (U2 : bv_unsigned (ew (am_env g pos c regs2 []) 2) = sp1)
  by (rewrite HE2; pose proof HC as (_ & _ & R2 & _); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (am_env g pos c regs2 []) 34) = shadow_addr (FA g pos))
  by (rewrite HE34; apply unsigned_lit_small; unfold SB in Hsh; lia).
assert (HRS : Forall (region_ok tfibsegs (am_env g pos c regs2 []) (mrestrict (w_H W2) mem2))
  [am_shadow_region 22 45 am_shm8]).
{ constructor; [|constructor]. rewrite am_shm8_eq.
  exact (am_shadow_region_ok B MT K XM_LIB LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 0 c [] 22 45
           HJ Hfr HC ltac:(lia) ltac:(lia)). }
assert (HAP : Forall (fun r => all_disjoint (am_env g pos c regs2 []) r am_regs) [am_shadow_region 22 45 am_shm8]).
{ unfold am_regs, am_regs0, cw_regs, am_shadow_region, am_spill_region, am_cur_region,
         stack_region, got_region, bcell_region.
  constructor; [|constructor].
  cbn [app all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U34.
  unfold A_GOT_shadow, A_shadow_glob, SB in *. repeat split; lia. }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 SH_F8 ly2 S2 W2 regs2 mem2 md2 0 c PC_HDB []
  [am_shadow_region 22 45 am_shm8] [] HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) HRS
  ltac:(cbn; repeat split; exact I) HAP I) as HS.
pose proof HJ as HJR.
assert (HAE0 : env_agree 35 (am_env g pos c regs2 []) (am_env g pos c regs2 [])) by apply env_agree_refl.
assert (SHOK : sh_ok tfibsegs CW_Bx [] (am_env g pos c regs2 []) (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((sp1 + 152 <= a < sp1 + 168) \/ (shadow_addr (FA g pos) + 22 <= a < shadow_addr (FA g pos) + 45)) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
unfold cfg_at. change (w64 PC_HDB) with (Z_to_bv 64 PC_HDB).
aj_run_to_sh tfibtbl_lib_ok HS HJR CA_MEMSET. { hd_awr_s sp1 U2 U34 EFA pos. }
cw_keep ltac:(hd_kwr_s U2 U34).
hd_shape W2 HS CA_MEMSET.
apply SRr_ret. unfold hd_ms1.
eapply am_mcut; [exact HJR | exact Hfr | lia | exact Hmo | |].
- eapply (am_exit B MT K XM_LIB LAWS);
  [ exact HC | exact HJR | idtac | exact HS | vm_compute; reflexivity
  | intros a Ha; unfold am_keepzone in Ha; apply KE;
    [unfold shadow_addr, SHADOW_OFF, SB in *; lia
    | intros [Hz | Hz]; unfold shadow_addr, SHADOW_OFF, SB in *; lia]
  | idtac
  | exact HPerm0 ].
  + env_agree_chain HAE0.
  + intros i Hi. rewrite <- am_shm0_eq.
    lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
      let r := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
      apply (am_sh_read_all Ev W2 (ms_mem msx) r (shadow_addr (FA g pos)) am_shm0);
      [ exact (st_ok_region_nth Ev ssx (restrict (w_H W2) msx) 5 r HS ltac:(vm_compute; reflexivity))
      | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; rewrite U34; reflexivity
      | vm_compute; reflexivity
      | vm_compute (Z.of_nat (length am_shm0)); lia ] end.
- split.
  + split; [lia|].
    lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
      rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx (26%bv : bv 5) HS) end.
    change (sr_get (ss_regs _) (26%bv : bv 5)) with (SOff 26 0).
    cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite HE26, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + split.
    { lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
        rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx (1%bv : bv 5) HS) end.
      change (sr_get (ss_regs _) (1%bv : bv 5)) with (SLit 527200). cbn [sv_denot]. reflexivity. }
    split.
    { lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
        rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx (10%bv : bv 5) HS) end.
      change (sr_get (ss_regs _) (10%bv : bv 5)) with (SOff 33 176).
      rewrite (am_den_off _ 33 (FA g pos) 176 ltac:(rewrite ?ew_ewset_other by lia; exact HE33)) by lia.
      reflexivity. }
    split.
    { lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
        rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx (11%bv : bv 5) HS) end.
      change (sr_get (ss_regs _) (11%bv : bv 5)) with (SLit 0). cbn [sv_denot]. reflexivity. }
    split.
    { lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
        rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx (12%bv : bv 5) HS) end.
      change (sr_get (ss_regs _) (12%bv : bv 5)) with (SLit 184). cbn [sv_denot]. reflexivity. }
    exists c, op. split; [|split; [exact Hc1 | split; [exact Hopr|]]].
    * unfold cur_at. split; [lia|]. split.
      -- hd_cur W2 HS sp1 U2 152 35%nat 0 (e_p g + c) HE35 ltac:(left; reflexivity).
      -- hd_cur W2 HS sp1 U2 160 36%nat 0 (e_n g - c) HE36 ltac:(right; left; reflexivity).
    * lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
        rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx (23%bv : bv 5) HS) end.
      change (sr_get (ss_regs _) (23%bv : bv 5)) with (SOff 23 0).
      cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite HE23, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- 0x80b5c: the checked memset of the call record ---- *)
Lemma hd_memset1 : forall g pos sp1 ops W2 c2, hd_ms1 B MT K XM_LIB g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (hd_mk B MT K XM_LIB g pos sp1 ops).
Proof using LAWS AMEMSET.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & H1 & H10 & H11 & H12
  & (c & op & Hcur & Hc1 & Hopr & H23)).
assert (Ek : k = 0) by (unfold EV_LIB in Hk; lia). subst k.
eapply (hd_memset_at B MT K XM_LIB LAWS AMEMSET _ g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 c 176 184 0 PC_HDK
  HJ Hfr HC Hcur H10 H11 H12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H1
  ltac:(apply ret_ok_even; vm_compute; reflexivity) ltac:(unfold PC_HDK; lia)
  (block_shadow_range (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + 176) 184 (FA g pos + 176) 184
     (am_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs2 mem2 md2 HC) ltac:(lia) ltac:(lia))).
intros regs3 mem3 md3 HJ3 HC3 Hcur3 HPR Hset KF.
assert (P26 : getr regs3 26 = getr regs2 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs3 23 = getr regs2 23) by exact (HPR 23 ltac:(unfold acallee_saved; lia)).
apply SRr_ret. unfold hd_mk.
eapply am_mcut; [exact HJ3 | exact Hfr | lia | exact Hmo | exact HC3 |].
split.
- split; [exact (proj1 Hops)|]. rewrite P26. exact (proj2 Hops).
- exists c, op. split; [exact Hcur3 | split; [exact Hc1 | split; [exact Hopr | split]]].
  + rewrite P23. exact H23.
  + intros j Hj. replace (FA g pos + 176 + j) with (FA g pos + 176 + j) by lia.
    rewrite (Hset j ltac:(lia)). reflexivity.
Qed.

(* ---- 0x80c08: the checked memset of before and out, which leaves the record k_rdZ ---- *)
Lemma hd_memset2 : forall g pos sp1 ops W2 c2, hd_mp B MT K XM_LIB g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (hd_mq B MT K XM_LIB g pos sp1 ops).
Proof using LAWS AMEMSET.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & H1 & H10 & H11 & H12
  & (c & kind & pv & dv & od & Hcur & Hc1 & Hkind & Hpd & H23 & Vkind & Vpv & Vdv & Z48 & Z24)).
assert (Ek : k = 0) by (unfold EV_LIB in Hk; lia). subst k.
assert (Hpvr : 0 <= pv < 2 ^ 64 /\ 0 <= dv < 2 ^ 64).
{ destruct Hpd as [(-> & -> & _) | [(-> & -> & _) | (-> & -> & _)]];
  unfold CA_PERS, CM_SPEC_C24, CM_SPEC_PC; lia. }
eapply (hd_memset_at B MT K XM_LIB LAWS AMEMSET _ g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 c 252 64 165 PC_HDQ
  HJ Hfr HC Hcur H10 H11 H12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H1
  ltac:(apply ret_ok_even; vm_compute; reflexivity) ltac:(unfold PC_HDQ; lia)
  (block_shadow_range (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + 176) 184 (FA g pos + 252) 64
     (am_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs2 mem2 md2 HC) ltac:(lia) ltac:(lia))).
intros regs3 mem3 md3 HJ3 HC3 Hcur3 HPR Hset KF.
assert (P26 : getr regs3 26 = getr regs2 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs3 23 = getr regs2 23) by exact (HPR 23 ltac:(unfold acallee_saved; lia)).
(* the bytes of the record at the return *)
assert (KZ : forall j, (4 <= j < 8 \/ 24 <= j < 76 \/ 140 <= j < 184) ->
  aview tfibsegs (w_H W2) mem3 (FA g pos + 176 + j) = Some 0).
{ intros j Hj. rewrite (KF (FA g pos + 176 + j) ltac:(lia) ltac:(lia)).
  destruct Hj as [Hj | Hj]; [apply Z48; lia | apply Z24; lia]. }
assert (KA : forall j, 76 <= j < 140 -> aview tfibsegs (w_H W2) mem3 (FA g pos + 176 + j) = Some 165).
{ intros j Hj. replace (FA g pos + 176 + j) with (FA g pos + 252 + (j - 76)) by lia.
  rewrite (Hset (j - 76) ltac:(lia)). reflexivity. }
assert (VZ : forall off (n : nat), (4 <= off /\ off + Z.of_nat n <= 8) \/ (24 <= off /\ off + Z.of_nat n <= 76)
  \/ (140 <= off /\ off + Z.of_nat n <= 184) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + off) n 0).
{ intros off n Hr. apply (hd_val_zero W2 mem3 (FA g pos + 176 + off) n).
  intros i Hi. replace (FA g pos + 176 + off + i) with (FA g pos + 176 + (off + i)) by lia.
  apply KZ. lia. }
assert (GZ : forall off (n : nat), (24 <= off /\ off + Z.of_nat n <= 76)
  \/ (140 <= off /\ off + Z.of_nat n <= 184) ->
  garr8 tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + off) (repeat 0 n)).
{ intros off n Hr. apply (hd_garr8_zero W2 mem3 (FA g pos + 176 + off) n).
  intros i Hi. replace (FA g pos + 176 + off + i) with (FA g pos + 176 + (off + i)) by lia.
  apply KZ. lia. }
assert (GA : forall off, (off = 76 \/ off = 108) ->
  garr8 tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + off) fa5).
{ intros off Hr. unfold fa5. apply (hd_garr8_val W2 mem3 (FA g pos + 176 + off) 32 165); [|lia].
  intros i Hi. replace (FA g pos + 176 + off + i) with (FA g pos + 176 + (off + i)) by lia.
  apply KA. cbn in Hi. lia. }
assert (VK : forall a (n : nat), FA g pos + 176 <= a -> a + Z.of_nat n <= FA g pos + 200 ->
  forall v, val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v ->
  val_mem tfibsegs (mrestrict (w_H W2) mem3) a n v).
{ intros a n Ho Hn v Hv. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
  intros x Hx. apply KF; lia. }
apply SRr_ret. unfold hd_mq.
eapply am_mcut; [exact HJ3 | exact Hfr | lia | exact Hmo | exact HC3 |].
split.
- split; [exact (proj1 Hops)|]. rewrite P26. exact (proj2 Hops).
- exists c, kind, pv, dv, od.
  split; [exact Hcur3|]. split; [exact Hc1|]. split; [exact Hkind|]. split; [exact Hpd|].
  split; [rewrite P23; exact H23|].
  split.
  + unfold kcall_atA, k_rdZ.
    cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc
         kz_want kz_want_len kz_want_key kz_want_display].
    split; [apply (VK (FA g pos + 176) 4%nat ltac:(lia) ltac:(cbn; lia)); exact Vkind|].
    split; [replace (FA g pos + 176 + 8) with (FA g pos + 184) by lia;
            apply (VK (FA g pos + 184) 8%nat ltac:(lia) ltac:(cbn; lia)); exact Vpv|].
    split; [replace (FA g pos + 176 + 16) with (FA g pos + 192) by lia;
            apply (VK (FA g pos + 192) 8%nat ltac:(lia) ltac:(cbn; lia)); exact Vdv|].
    split; [apply (VZ 24 4%nat); cbn; lia|].
    split; [apply (VZ 28 4%nat); cbn; lia|].
    split; [apply (VZ 32 4%nat); cbn; lia|].
    split; [apply (VZ 36 4%nat); cbn; lia|].
    split; [apply (GZ 40 24%nat); cbn; lia|].
    split; [apply (VZ 64 8%nat); cbn; lia|].
    split; [apply (VZ 72 4%nat); cbn; lia|].
    split; [apply (GA 76); left; reflexivity|].
    split; [apply (GA 108); right; reflexivity|].
    split; [apply (VZ 140 4%nat); cbn; lia|].
    split; [apply (GZ 144 24%nat); cbn; lia|].
    split; [apply (VZ 168 8%nat); cbn; lia|].
    split; [apply (VZ 176 4%nat); cbn; lia | apply (VZ 180 4%nat); cbn; lia].
  + unfold kcall_wfZ, k_rdZ.
    cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc
         kz_want kz_want_len kz_want_key kz_want_display].
    repeat split; try lia; try (apply repeat_length).
Qed.

(* ================================ the segment ================================ *)
Theorem seg_head_holds : seg_head B MT K XM_LIB.
Proof using MTL TL LAWS ML AMEMSET GM POF ROB.
unfold seg_head. intros g pos sp1 ops W2 c2 H.
eapply SRr_bind; [exact (hd_a1 g pos sp1 ops W2 c2 H)|].
intros W3 c3 _ [HX | HB]; [apply SRr_ret; left; exact HX|].
eapply SRr_bind; [exact (hd_a2 g pos sp1 ops W3 c3 HB)|]. intros W4 c4 _ H4.
eapply SRr_bind; [exact (hd_memset1 g pos sp1 ops W4 c4 H4)|]. intros W5 c5 _ H5.
eapply SRr_bind; [exact (hd_b B MT K XM_LIB TL LAWS ML g pos sp1 ops W5 c5 H5)|]. intros W6 c6 _ H6.
eapply SRr_bind; [exact (hd_mid B MT K XM_LIB TL LAWS ML GM MTL POF g pos sp1 ops W6 c6 H6)|].
intros W7 c7 _ H7.
eapply SRr_bind; [exact (hd_memset2 g pos sp1 ops W7 c7 H7)|]. intros W8 c8 _ H8.
eapply SRr_bind; [exact (hd_tail B MT K XM_LIB TL LAWS ML g pos sp1 ops W8 c8 H8)|].
intros W9 c9 _ (kind & H9). apply SRr_ret. right. exists kind. exact H9.
Qed.
End d.
End b.
