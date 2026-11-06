(* The tail of the HEAD segment of the image-A walk of LLVMFuzzerTestOneInput (0x80c0c-0x80c30): from the cut
   hd_mq of lib/A/Prog/codec_amain_head_cut.v (the record as HEAD leaves it, k_rdZ kind pv dv) to the readers' cut
   inv_rd of lib/A/Prog/codec_amain_inv.v.
     0x80c0c lw a0,0(s6) the kind; 0x80c14 bltu 13,a0: kind 14 to MASKS 0x81208;
     0x80c18-0x80c30 kind 0 .. 13: the switch table at 0x20eac (14 words of the read-only image), jr to rd_pc kind.
   No instrumented check and no store. The walk is split on the kind (0 .. 14) first, so the record's kind is a
   literal of the state's region at F + 176 and every address of the run is a literal: the kind run stops before
   the table load (0x80c28), the record's region is then replaced by the table's, and a second run reaches the
   reader. The end cut is the exit bridge's (codec_amain_st.am_exit, am_mcut); the record's bytes, the cursor and
   the 56 shadow bytes are kept (the only write window of the state is the cursor's, which the runs do not use). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkImg CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem codec_amain_encl codec_amain_head_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the record's kind as a literal of the frame's region, and the switch table *)
Definition ht_rk (n : Z) : YP09.region := am_frame_region 176 180 176 176 [YP09.mkChunk 176 (CVal 4 (SLit n))].
Definition ht_rt : YP09.region := cpg_img_region 0x20eac 56.
Definition HT_LD : Z := 0x80c28.

(* the write premise of a run: every region read-only but the cursor, the walk's stack window *)
Ltac ht_awr sp1 U2 :=
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | lazymatch goal with |- awr_ok _ _ _ ?sp0 _ _ _ _ _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ sp0 _ _ _ _ _ 2%nat (sp1 - sp0)) end;
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
(* the zone of its windows: the cursor *)
Ltac ht_kwr U2 :=
  idtac;
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U2 in Hb; lia | ]);
  destruct Hr.
(* keep the regions of the state at the indices l *)
Ltac ht_keep HS l :=
  lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
    let l0 := eval vm_compute in (ss_mem ssv) in
    let rs := eval vm_compute in (map (fun i => nth i l0 got_region) l) in
    let HS1 := fresh "HS" in
    assert (HS1 : st_ok tfibsegs Ev (mkSS (ss_pc ssv) (ss_regs ssv) rs (ss_resv ssv) (ss_facts ssv)) msv)
    by (apply (st_ok_submem tfibsegs Ev ssv msv rs HS); [change (submem rs l0); submem_to | reflexivity]);
    clear HS; rename HS1 into HS end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.

(* a record whose bytes are kept is the same record *)
Lemma ht_k_kept : forall (W W' : world tfibsegs) mem mem' q k,
kcall_atA tfibsegs W mem q k -> kcall_wfZ k ->
(forall x, q <= x < q + 184 -> aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) ->
kcall_atA tfibsegs W' mem' q k.
Proof.
intros W W' mem mem' q k Hk Hwf Hkp.
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lo & _).
pose proof Hk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G108 & _).
assert (E : k = kz_set_out k (kz_out k)) by (destruct k; reflexivity).
rewrite E. apply (kcall_at_out W W' mem mem' q k (kz_out k) Hk Hwf).
- intros x Hx _. apply Hkp. exact Hx.
- apply (am_garr8_kept (w_H W) (w_H W') mem mem'); [|exact G108].
  intros x Hx. apply Hkp. rewrite Lo in Hx. cbn in Hx. lia.
Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).


(* the tail for one kind, written once: n is a literal when it runs *)
Ltac ht_go n :=
  lazymatch goal with
  | HS0 : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HRk : region_ok _ _ _ (ht_rk _),
    U2 : bv_unsigned (ew _ 2) = ?sp1, U33 : bv_unsigned (ew _ 33) = _ |- _ =>
  (* the base regions but the .got slot and the cell, then the record's kind *)
  ht_keep HS0 [0; 3; 4]%nat;
  lazymatch goal with HSx : st_ok _ ?Ev _ _ |- _ =>
    pose proof (ast_ok_add_region tfibsegs Ev _ _ (ht_rk n) HSx eq_refl HRk
      ltac:(cbn [ss_mem]; unfold ht_rk, am_frame_region, stack_region, am_spill_region, am_cur_region;
            cbn [all_disjoint]; unfold extent_disjoint;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U33, U2;
            repeat split; lia)) as HS2;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HSx; rename HS2 into HS end
  end.

Lemma hd_tail_n : forall n g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c pv dv od,
0 <= n <= 14 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> 1 <= c -> pd_okA pv dv od -> getr regs2 23 = w64 pv ->
k_at g pos (k_rdZ n pv dv) W2 mem2 ->
SRr tfibsegs W2 (cfg_at tfibsegs PC_HDQ regs2 mem2 md2)
  (fun W3 c3 => exists kind, inv_rd B MT K XM_LIB g pos sp1 ops kind W3 c3).
Proof using TL LAWS ML ROB.
intros n g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c pv dv od Hn HJ Hfr Hk Hmo HC Hops Hcur Hc1 Hpd H23 Hkat.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold AM_HI in Hchi.
pose proof HC as (Hpre & _ & R2 & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof HC as HPerm0. do 45 (destruct HPerm0 as (_ & HPerm0)).
destruct Hops as (Hops1 & Hops2).
pose proof Hcur as (Hc & C152 & C160).
destruct Hkat as (Hkat & Hkwf).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF. split; [apply Z.add_le_mono_l; apply Z.div_le_lower_bound; lia|].
  apply Z.add_le_mono_l. apply Z.div_le_upper_bound; lia. }
unfold SB in Hsh.
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c PC_HDQ [] [] []
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) I) as HS0.
assert (HRk : region_ok tfibsegs (am_env g pos c regs2 []) (mrestrict (w_H W2) mem2) (ht_rk n)).
{ apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c [] 176 180 176 176 _
    HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs _ _ (FA g pos) 176 4 (SLit n) n); [reflexivity | cbn; lia | cbn; lia |].
  exact (proj1 Hkat). }
assert (HE2 : ew (am_env g pos c regs2 []) 2 = getr regs2 2) by exact (am_ew_reg g pos c regs2 [] 2 2%bv eq_refl).
assert (U2 : bv_unsigned (ew (am_env g pos c regs2 []) 2) = sp1)
  by (rewrite HE2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (am_env g pos c regs2 []) 33) = FA g pos)
  by (rewrite (am_ew_F g pos c regs2 []); apply unsigned_lit_small; lia).
assert (HE23 : ew (am_env g pos c regs2 []) 23 = getr regs2 23) by exact (am_ew_reg g pos c regs2 [] 23 23%bv eq_refl).
assert (HE26 : ew (am_env g pos c regs2 []) 26 = getr regs2 26) by exact (am_ew_reg g pos c regs2 [] 26 26%bv eq_refl).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 152 <= a < sp1 + 168) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
unfold cfg_at. change (w64 PC_HDQ) with (Z_to_bv 64 PC_HDQ).
ht_go n.
(* the end of the run at rd_pc n: the cut *)
assert (Hend : forall W3 regs3 mem3 md3 ly3 S3 k3 ss3 pc3,
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
  ly3 = ly2 -> S3 = S2 -> k3 = k -> W3 = W2 ->
  st_ok tfibsegs (am_env g pos c regs2 []) ss3 (restrict (w_H W3) (mkst regs3 pc3 mem3 (seg_rom tfibsegs))) ->
  am_keep_ok (ss_regs ss3) = true ->
  sr_get (ss_regs ss3) (26%bv : bv 5) = SOff 26 0 -> sr_get (ss_regs ss3) (23%bv : bv 5) = SOff 23 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 152 <= a < sp1 + 168) ->
     aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  val_mem tfibsegs (mrestrict (w_H W3) mem3) (sp1 + 152) 8 (e_p g + c) ->
  val_mem tfibsegs (mrestrict (w_H W3) mem3) (sp1 + 160) 8 (e_n g - c) ->
  pc3 = Z_to_bv 64 (rd_pc n) ->
  inv_rd B MT K XM_LIB g pos sp1 ops n W3 (mkCfg (mkst regs3 pc3 mem3 (seg_rom tfibsegs)) md3)).
{ intros W3 regs3 mem3 md3 ly3 S3 k3 ss3 pc3 HJ3 -> -> -> -> HS3 Hkeep R26 R23 KE3 V152 V160 ->.
  assert (HC3 : mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs3 mem3 md3).
  { eapply (am_exit B MT K XM_LIB LAWS); [exact HC | exact HJ3 | apply env_agree_refl | exact HS3 | exact Hkeep
    | | | exact HPerm0].
    - intros a Ha. unfold am_keepzone in Ha. apply KE3; [lia|]. lia.
    - intros i Hi. rewrite KE3 by lia. exact (HSH i Hi). }
  unfold inv_rd. eapply am_mcut; [exact HJ3 | exact Hfr | lia | exact Hmo | exact HC3 |].
  assert (G26 : getr regs3 26 = getr regs2 26).
  { rewrite (st_ok_restrict_reg tfibsegs (w_H W2) _ ss3 _ (26%bv : bv 5) HS3). cbn [ms_regs mkst restrict].
    rewrite R26. cbn [sv_denot]. rewrite HE26, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (G23 : getr regs3 23 = getr regs2 23).
  { rewrite (st_ok_restrict_reg tfibsegs (w_H W2) _ ss3 _ (23%bv : bv 5) HS3). cbn [ms_regs mkst restrict].
    rewrite R23. cbn [sv_denot]. rewrite HE23, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  split; [split; [exact Hops1 | rewrite G26; exact Hops2]|].
  split; [lia|].
  exists c, pv, dv, od.
  split; [split; [exact Hc | split; [exact V152 | exact V160]]|].
  split; [exact Hc1|]. split; [exact Hpd|]. split; [rewrite G23; exact H23|].
  split; [|exact Hkwf].
  apply (ht_k_kept W2 W2 mem2 mem3 (FA g pos + 176) (k_rdZ n pv dv) Hkat Hkwf).
  intros x Hx. apply KE3; lia. }
(* the read-only image at any state of the journal, for the switch table's region *)
assert (HRO : forall ly3 S3 W3 mem3 md3 k3,
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
  arodata_okP tfibsegs CA_RLO CA_RHI B (aview tfibsegs (w_H W3) mem3))
  by (intros ly3 S3 W3 mem3 md3 k3 HJ3; exact (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly3 S3 W3 mem3 md3 k3 Hpre HJ3)).
assert (HT0 : forall a, 0x20eac <= a < 0x20eac + 56 ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
  by (intros a Ha; apply (tl_lib_consts B TL); unfold lib_const_addr; lia).
assert (Hn' : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/
  n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14) by lia.
clear Hn.
repeat (destruct Hn' as [-> | Hn']); [ .. | subst n].
(* kind 0 .. 13: the kind run to the table load, the table's region in place of the record's, the run to the reader *)
1-14: aj_run_to_sh tfibtbl_lib_ok HS HJ HT_LD; [ht_awr sp1 U2 | cw_keep ltac:(ht_kwr U2); ht_keep HS [1; 2; 3]%nat;
  lazymatch goal with HS : st_ok _ ?Ev _ (restrict _ ?msx), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (ast_ok_add_region tfibsegs Ev _ _ ht_rt HS eq_refl
      (cpg_img_region_ok B CA_RLO CA_RHI Ev W2 (ms_mem msx) 0x20eac 56 (HRO _ _ _ _ _ _ HJx) (am_in_ro 0x20eac 56 eq_refl)
         (fun a Ha => proj1 (HT0 a Ha)) (fun a Ha => proj2 (HT0 a Ha)) eq_refl ltac:(lia) ltac:(lia) ltac:(lia))
      ltac:(cbn [ss_mem]; unfold ht_rt, cpg_img_region; cbn [all_disjoint]; unfold extent_disjoint;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U2; repeat split; lia)) as HS2;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS; rename HS2 into HS' end ].
1-14: rename HS' into HS.
1-14: lazymatch goal with HRk : region_ok _ _ _ (ht_rk ?n) |- _ =>
  let pc := eval vm_compute in (rd_pc n) in
  aj_run_to_sh tfibtbl_lib_ok HS HJ pc; [ht_awr sp1 U2 | cw_keep ltac:(ht_kwr U2)] end.
(* kind 14: bltu taken, one run to MASKS *)
15: aj_run_to_sh tfibtbl_lib_ok HS HJ 0x81208; [ht_awr sp1 U2 | cw_keep ltac:(ht_kwr U2)].
(* the end cut, for every kind *)
all: lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict _ ?msx), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let Hshape := fresh "Hshape" in
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) Ev ssx msx HS eq_refl) as Hshape;
  rewrite Hshape in HS |- *; clear Hshape;
  apply SRr_ret;
  let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
  let HR := fresh "HR" in
  pose proof (st_ok_region_nth Ev ssx _ 3 r3 HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem mkst restrict] in HR;
  eexists; eapply Hend;
  [ exact HJx | reflexivity | reflexivity | reflexivity | reflexivity | exact HS
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact KE
  | apply (field_of_region Ev _ 2 sp1 _ _ _ _ _ 152 8 (SOff 35 0) (e_p g + c) HR U2);
    [ cbn [In]; left; reflexivity
    | cbn [sv_denot]; rewrite (am_ew_CP g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold AM_HI in *; cbn; lia | cbn; lia ]
  | apply (field_of_region Ev _ 2 sp1 _ _ _ _ _ 160 8 (SOff 36 0) (e_n g - c) HR U2);
    [ cbn [In]; right; left; reflexivity
    | cbn [sv_denot]; rewrite (am_ew_CN g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold AM_HI in *; cbn; lia | cbn; lia ]
  | vm_compute; reflexivity ] end.
Qed.

(* the tail from the cut hd_mq at 0x80c0c *)
Lemma hd_tail : forall g pos sp1 ops W2 c2, hd_mq B MT K XM_LIB g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => exists kind, inv_rd B MT K XM_LIB g pos sp1 ops kind W3 c3).
Proof using TL LAWS ML ROB.
intros g pos sp1 ops W2 c2
  (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops &
   (c & kind & pv & dv & od & Hcur & Hc1 & Hkind & Hpd & H23 & Hkat)).
exact (hd_tail_n kind g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c pv dv od Hkind HJ Hfr Hk Hmo HC Hops Hcur Hc1 Hpd H23 Hkat).
Qed.
End b.
End a.
