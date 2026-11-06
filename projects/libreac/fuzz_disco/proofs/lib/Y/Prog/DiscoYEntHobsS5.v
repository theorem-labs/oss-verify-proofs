(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntCls.v, with its module paths and module names changed; 323 of its 424 lines of code are new or changed and 1172 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_frame_clean_len_c slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntClsCuts DiscoYEntHobsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require RoleOf CheckTable CheckSighting.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition hb_acs : list YP09.chunk := [YP09.mkChunk 184 (CVal 8 (SOff (AT_X + 32) 0))].
Ltac hb_ro HS bn :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs bn in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0
     (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma hb_env_old : forall cx E vals q, (q < AT_FL)%nat -> ew (d_env cx E vals) q = ew E q.
Proof. intros cx E vals q Hq. unfold d_env. apply ew_havoc_old. exact Hq. Qed.
Lemma hb_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma hb_aview_ext : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' HM a. unfold aview, mbyte, mrestrict. rewrite HM. reflexivity. Qed.
Lemma hb_val_ext : forall (W : world SEGS) (m m' : word -> option byte) a w v,
  (forall x, m' x = m x) -> val_mem SEGS (rd W m) a w v -> val_mem SEGS (rd W m') a w v.
Proof.
intros W m m' a w v HM Hv. eapply val_mem_aview_kept_x; [|exact Hv]. intros x _. apply hb_aview_ext. exact HM.
Qed.
Lemma hb_garr_ext : forall (W : world SEGS) (m m' : word -> option byte) a l,
  (forall x, m' x = m x) -> garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
intros W m m' a l HM Hg. eapply garr8_aview_kept; [|exact Hg]. intros x _. apply hb_aview_ext. exact HM.
Qed.
Definition HB_P5 : Z := 0xea8.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis TCHKT : CheckTable.tcheck_table_spec B.
Hypothesis BRT : d_body_rt_stmt B.

Lemma hb_body_mem : forall cx h n xb ly3 S3 (W : world SEGS) mem3 m4 md k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W m4 md k ->
  d_body B cx h n xb dsh_rec ly3 S3 W mem3 -> (forall x, m4 x = mem3 x) ->
  d_body B cx h n xb dsh_rec ly3 S3 W m4.
Proof.
intros cx h n xb ly3 S3 W mem3 m4 md k HC Hbody Hpt.
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m4 md k HC) as (Hal16 & Hlo & Hhi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (Hav : forall a, aview SEGS (w_H W) m4 a = aview SEGS (w_H W) mem3 a) by (apply hb_aview_ext; exact Hpt).
apply (BRT cx h n n xb dsh_rec dsh_rec ly3 S3 W mem3 m4 (d_A cx) (d_A cx) (fun _ => False) Hbody).
- unfold LLVMF_STK, MFRAME in *; lia.
- unfold MFRAME in HA1; lia.
- intros a [].
- intros a _ _. exact (Hav a).
- intros a _ [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hpt. exact Hb.
- exact (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h dsh_rec W mem3 ly3 S3 W m4 md k HC Hframe (fun a _ => Hav a)).
- exact (cl_shadow_keep cx dsh_rec W W mem3 m4 Hshadow (fun a _ => Hav a)).
- pose proof Hbody as (_ & _ & _ & _ & _ & _ & _ & _ & (Hn & _) & _). lia.
Qed.

Lemma hb5_tail : forall cx h i n now op nb fr len W c,
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx HB_P5 h i n now (dxb fr len) dsh_rec (fun _ => True)
    (hb_X cx op nb fr len) W c ->
  SRr SEGS W c (r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len).
Proof.
intros cx h i n now op nb fr len W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & _ & HX & Hsp0 & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof (cl_regs_ok B cx E regs [] HdE HrL HAr2) as HROK.
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HB_P5 cl_sr (cl_vals regs [])
  [] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag HROK
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs []) [] [] HctxD HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
hb_ro HS 516%nat. hb_ro HS 529%nat. hb_ro HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs []))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [])) (rd W mem3)) by constructor.
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + HB_P5)) with (Z_to_bv 64 (BASE + HB_P5)).
paj_run_to_tok RUNTO HS HJ SHOK cl_span R27_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := cl_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r0 = getr regs r0).
{ intros r0 Hr0. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r0 HS), (HROK r0).
  cbv [In] in Hr0. repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (hb_body_mem cx h n (dxb fr len) ly3 S3 W mem3 (ms_mem ms) md4 k HC4 Hbody Hpt) as Hbody4.
pose proof HX as (Hop & Hop2 & (F1 & F2 & F3 & F4) & (S200 & S328 & S368 & S408) & (S360 & S352) & Hlen & Hnb).
apply SRr_ret. rewrite Hms. unfold r27_in, d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
split; [reflexivity|]. split; [exact Hfrm0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [lia|]. split; [exact Hnow|].
split.
{ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL, spZ in *.
  rewrite !RG by (cbv; tauto). repeat split; assumption. }
split; [exact I|].
split.
{ split; [exact (conj F1 (conj F2 (conj F3 (hb_garr_ext W mem3 (ms_mem ms) _ _ Hpt F4))))|].
  split; [exact (conj (hb_val_ext W mem3 (ms_mem ms) _ _ _ Hpt S200) (conj (hb_val_ext W mem3 (ms_mem ms) _ _ _ Hpt S328)
    (conj (hb_val_ext W mem3 (ms_mem ms) _ _ _ Hpt S368) (hb_val_ext W mem3 (ms_mem ms) _ _ _ Hpt S408))))|].
  split; [exact Hlen | reflexivity]. }
split; [destruct Hsp0 as (P1 & P2); exact (conj (hb_val_ext W mem3 (ms_mem ms) _ _ _ Hpt P1) (hb_val_ext W mem3 (ms_mem ms) _ _ _ Hpt P2))|].
apply (cl_body_n B cx h n (nb - len) (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) Hbody4). lia.
Qed.

Lemma hb_kept_ro : forall ly3 S3 (W : world SEGS) m3 md3 W2 m2 lo hi,
  AR SEGS B ly3 S3 W m3 md3 -> alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m3 a) ->
  (forall a, lo <= a < hi -> apresent (w_H W2) m2 a) ->
  cl_kept B ly3 S3 W m3 W2 m2 lo hi (fun _ => False).
Proof.
intros ly3 S3 W m3 md3 W2 m2 lo hi HAR Hlo Hhi HK HP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [intros a Ha Hn _; apply HK; [lia | exact Hn]|].
split.
{ intros b m i Hin Hi _. destruct (al_blocks _ _ LAWS ly3 S3 W m3 md3 b m HAR Hin) as (_ & Hb0 & Hbc & _).
  apply HK; lia. }
split.
{ intros a Hi _ _. pose proof (pa_img_range a Hi) as Ra. apply HK; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Ra; lia. }
split.
{ intros cid pos a Hin Hr _. destruct (frames_bounds _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (HF0 & HFc & HFia).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  assert (Hsh : shadow_addr (frame_addr ly3 cid pos) + fs_frame_bytes cid / 8 <= alloc_ceiling).
  { pose proof (shadow_addr_bounds (frame_addr ly3 cid pos) ltac:(unfold kHighMemEnd in *; lia)) as HSH.
    assert (Hd : fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
    unfold shadow_addr, SHADOW_OFF in *. unfold kLowMemEnd, kHighShadowEnd in *.
    pose proof (Z.div_le_upper_bound (frame_addr ly3 cid pos) 8 (frame_addr ly3 cid pos) ltac:(lia) ltac:(lia)). lia. }
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
  pose proof (shadow_addr_bounds (frame_addr ly3 cid pos) ltac:(unfold kHighMemEnd in *; lia)) as HSH.
  unfold kLowMemEnd, kHighShadowEnd in HSH.
  apply HK; destruct Hr as [Hr | Hr]; lia. }
split.
{ intros a Ha Hn Hp. apply (apresent_transfer SEGS (w_H W) (w_H W2) m3 m2 a); [lia | | apply HK; [lia | exact Hn] | exact Hp].
  intros Hi. pose proof (pa_img_range a Hi) as Ra. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Ra. lia. }
exact HP.
Qed.

Theorem hb_L5 : hb_L5_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold hb_L5_stmt. intros cx h i n now op nb fr len W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & _ & HX & Hsp0 & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & V184 & Hrest).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
destruct (hb_hblk_read B MT XM_LIB RLO RHI tfib_K LAWS cx h n (dxb fr len) dsh_rec ly3 S3 W mem3 md3 k
  CheckTable.TCHECK_TABLE_STK HctxD Hbody ltac:(unfold CheckTable.TCHECK_TABLE_STK, ESTACK; lia))
  as (Hhin & Hh0 & Hh8 & Hh63 & Hhmr & Hhra & Hhsv & Hhoi & Hhstk & Hhsep & Hhpres).
assert (Hh64 : 0 <= h < 2 ^ 64) by (clear - Hh0 Hh63; unfold HUNT_SIZE in *; lia).
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs [w64 h])) (rd W mem3) (d_A cx)) hb_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 184 8%N (SOff (AT_X + 32) 0) h).
  - cbn [sv_denot]. rewrite Z.add_0_r.
    rewrite (hb_env_x cx E (cl_vals regs [w64 h]) 32%nat
      ltac:(unfold cl_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia)).
    unfold cl_vals. cbn [map seq app nth]. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hh64.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. exact V184. }
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HB_P4 cl_sr (cl_vals regs [w64 h])
  hb_acs [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (cl_regs_ok B cx E regs [w64 h] HdE HrL HAr2)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs [w64 h]) [] [] HctxD HdE I I)
  HACS (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
hb_ro HS 516%nat. hb_ro HS 529%nat. hb_ro HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs [w64 h]))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [w64 h])) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + HB_P4)) with (Z_to_bv 64 (BASE + HB_P4)).
paj_run_tok RUN HS HJ SHOK cl_span.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := cl_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
rewrite (pa_sigma_check_table (PI := PI)) in HS.
pose proof (cl_regs_ok B cx E regs [w64 h] HdE HrL HAr2) as HROK.
assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r0 = getr regs r0).
{ intros r0 Hr0. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r0 HS), (HROK r0).
  cbv [In] in Hr0. repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + HB_P5)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  unfold w64, HB_P5. exact (codeptr_val _ 3752 HEI). }
assert (A10 : getr (ms_regs ms) 10 = w64 h).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite Z.add_0_r.
  change (ew (d_env cx E (cl_vals regs [w64 h])) 563) with (ew (d_env cx E (cl_vals regs [w64 h])) (AT_X + 32)).
  rewrite (hb_env_x cx E (cl_vals regs [w64 h]) 32%nat
    ltac:(unfold cl_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia)).
  unfold cl_vals. cbn [map seq app nth]. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (hb_body_mem cx h n (dxb fr len) ly3 S3 W mem3 (ms_mem ms) md4 k HC4 Hbody Hpt) as Hbody4.
pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4 & Hshadow4 & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & _).
pose proof Hframe4 as (E4 & HdE4 & Hregs4 & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k HC4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR4 & _ & _ & _).
destruct (cl_achain B MT XM_LIB XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k E4 (d_A cx) HC4 HdE4 (Forall_inv Hregs4)
  ltac:(unfold MFRAME in HA1; lia)) as (ch & Hch).
pose proof Hobjs4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LH4 & GH4 & OKH4 & _).
pose proof OKH4 as (_ & TOK4 & _).
pose proof TOK4 as (T1 & T2 & T3 & _).
assert (ES : sub H4 0 400 = firstn 400 H4) by (unfold sub; cbn [skipn]; reflexivity).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
assert (Hsp4 : spZ (ms_regs ms) = d_A cx) by (unfold spZ in *; rewrite RG by (cbv; tauto); exact Hsp).
assert (Es0 : s0Z (ms_regs ms) = d_S cx).
{ unfold s0Z. rewrite RG by (cbv; tauto). rewrite H8. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
assert (HE2 : bv_unsigned (ew (d_env cx E (cl_vals regs [w64 h])) 2) = d_S cx).
{ rewrite hb_env_old by (unfold AT_FL; lia). destruct HdE as (HER & _). rewrite (HER 2%nat 2%bv eq_refl). reflexivity. }
assert (Ho16 : (d_A cx - d_S cx) mod 16 = 0) by (clear - HA2 Hal16; lia).
eapply SRr_bind.
{ eapply (hb_aj_call B LAWS) with (STK1 := CheckTable.TCHECK_TABLE_STK) (FP1 := []) (EV1 := 0)
    (o := d_A cx - d_S cx) (raw := getr (ms_regs ms) 1) (ch1 := ch);
  [ exact HS
  | reflexivity
  | exact HJ
  | rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 2%bv HS);
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    cbn [sv_denot]; rewrite HE2;
    rewrite hb_env_old by (unfold AT_FL; lia);
    destruct HdE as (_ & _ & _ & HA60 & _); change AT_A with 60%nat in HA60; rewrite HA60;
    unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
  | reflexivity
  | exact HE2
  | exact Ho16
  | unfold MFRAME in HA1; lia
  | unfold CheckTable.TCHECK_TABLE_STK, ESTACK; lia
  | unfold CheckTable.TCHECK_TABLE_STK, ESTACK, MFRAME, LLVMF_STK in *; lia
  | rewrite RG by (cbv; tauto); exact Hgp
  | rewrite RG by (cbv; tauto); exact Htp
  | reflexivity
  | rewrite R1; unfold HB_P5; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite R1; unfold w64; pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _);
    rewrite unsigned_lit_small by (unfold HB_P5; lia); pose proof (pa_base_lo (PI := PI)); unfold IMG_LO, HB_P5 in *; lia
  | replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) by lia; rewrite Es0; exact Hch
  | intros _
  | intros a (rr & [] & _) ].
  cbn [ss_pc setpc].
  assert (Esp8 : spZ (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) = spZ (ms_regs ms))
    by (unfold spZ; rewrite getr_other by reg_neq_tac; reflexivity).
  pose proof (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md4 k (regupd (ms_regs ms) 8 (Z_to_bv 64 0))
    CheckTable.TCHECK_TABLE_STK (d_A cx - d_S cx) [] HJ) as HPRE2.
  specialize (HPRE2 ltac:(rewrite Esp8, Hsp4; lia) Ho16 ltac:(unfold MFRAME in HA1; lia)
    ltac:(unfold CheckTable.TCHECK_TABLE_STK, ESTACK; lia)
    ltac:(unfold CheckTable.TCHECK_TABLE_STK, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  specialize (HPRE2 ltac:(rewrite getr_other by reg_neq_tac; rewrite R1; unfold HB_P5; apply ret_ok_codeptr_v; [lia | reflexivity])).
  specialize (HPRE2 ltac:(unfold raZ; rewrite getr_other by reg_neq_tac; rewrite R1; unfold w64;
    pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _);
    rewrite unsigned_lit_small by (unfold HB_P5; lia); pose proof (pa_base_lo (PI := PI)); unfold IMG_LO, HB_P5 in *; lia)).
  specialize (HPRE2 ltac:(rewrite getr_other by reg_neq_tac; rewrite RG by (cbv; tauto); exact Hgp)).
  specialize (HPRE2 ltac:(rewrite getr_other by reg_neq_tac; rewrite RG by (cbv; tauto); exact Htp)).
  specialize (HPRE2 ltac:(apply achain_low; unfold s0Z; rewrite getr_same by reg_neq_tac;
    rewrite unsigned_lit_small by lia; lia)).
  pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)) as Hrq.
  pose proof (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 h HUNT_SIZE h 400 HAR4 Hhin
    ltac:(lia) ltac:(unfold HUNT_SIZE in *; lia)) as HMR.
  pose proof (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 h HUNT_SIZE h 400 HAR4 Hhin
    ltac:(lia) ltac:(unfold HUNT_SIZE in *; lia)) as HRA.
  pose proof (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 h HUNT_SIZE h 400 HAR4 Hhin
    ltac:(lia) ltac:(unfold HUNT_SIZE in *; lia) ltac:(lia)) as HSV.
  apply (TCHKT fq ly3 S3 W (ms_regs ms) (ms_mem ms) md4 [] h (sub H4 0 400) HPRE2 Himg4 A10 Hh0 Hh8
    ltac:(unfold HUNT_SIZE in Hh63; lia)).
  - unfold sub. rewrite length_firstn, length_skipn, LH4. reflexivity.
  - rewrite ES. apply cl_garr8_firstn. exact GH4.
  - exact HMR.
  - exact HRA.
  - exact HSV.
  - left. rewrite Hsp4. unfold HUNT_SIZE in Hhstk. lia.
  - unfold off_img in *. unfold HUNT_SIZE in Hhoi. lia.
  - rewrite ES. exact T1.
  - rewrite ES. exact T2.
  - rewrite ES. exact T3. }
intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hcsr2 & HJ2 & HJc & HPR & HPerm & HKV).
rewrite Z.add_0_r in HJ2.
replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) in HJc by lia.
pose proof HJc as (_ & _ & _ & _ & _ & Hfr2 & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
cbn [app] in Hfr2.
assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
  by (split; [exact Hbase | split; [exact HJ2 | rewrite Hfr2; exact Hfrs]]).
assert (HKT : cl_kept B ly3 S3 W (ms_mem ms) W2 mem2 (d_A cx - CheckTable.TCHECK_TABLE_STK) (d_A cx) (fun _ => False)).
{ apply (hb_kept_ro ly3 S3 W (ms_mem ms) md4 W2 mem2 _ _ HAR4).
  - unfold CheckTable.TCHECK_TABLE_STK, ESTACK, MFRAME, LLVMF_STK in *. lia.
  - lia.
  - intros a Ha Hnw. rewrite <- Hsp4 in Hnw. exact (HKV a Ha Hnw).
  - intros a Ha. apply HPJ. exact Ha. }
assert (VK : forall off v, 0 <= off -> off + 8 <= 472 -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W2 mem2) (d_A cx + off) 8 v).
{ intros off v Ho1 Ho2 Hv.
  exact (cl_slot_keep B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k W2 mem2 _ _ (fun _ => False)
    off v HC4 HKT ltac:(lia) (fun a Ha => match Ha with end) Ho1 Ho2 Hv). }
pose proof HX as (Hop & Hop2 & (F1 & F2 & F3 & F4) & (S200 & S328 & S368 & S408) & (S360 & S352) & Hlen & Hnb).
assert (Hfrm4 : d_frm cx nb fr len W (ms_mem ms))
  by exact (conj F1 (conj F2 (conj F3 (hb_garr_ext W mem3 (ms_mem ms) _ _ Hpt F4)))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite RG by (cbv; tauto); exact Hgp).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite RG by (cbv; tauto); exact Htp).
assert (Q8 : getr (ms_regs ms) 8 = w64 (d_S cx)) by (rewrite RG by (cbv; tauto); exact H8).
assert (Q9 : getr (ms_regs ms) 9 = w64 (d_A cx)) by (rewrite RG by (cbv; tauto); exact H9).
assert (Q19 : getr (ms_regs ms) 19 = w64 SHADOW_OFF) by (rewrite RG by (cbv; tauto); exact H19).
assert (Q18 : getr (ms_regs ms) 18 = w64 WS_MASK) by (rewrite RG by (cbv; tauto); exact H18).
assert (Q20 : getr (ms_regs ms) 20 = w64 32) by (rewrite RG by (cbv; tauto); exact H20).
assert (Q27 : getr (ms_regs ms) 27 = w64 (shadow_addr (d_FB cx))) by (rewrite RG by (cbv; tauto); exact H27).
apply (hb5_tail cx h i n now op nb fr len).
unfold d_arm_at_pf, d_at.
exists fx2, ly2, S2, regs2, mem2, md2, k, acc.
split; [unfold cfg_at; rewrite R1; reflexivity|].
split; [exact (hb_frm0_post fq fx2 Hfrm0 Hcsr2)|].
split; [exact Hbase|]. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|]. split; [exact Hk|].
split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rL. unfold spZ in Hsp4 |- *.
  assert (E2 : getr regs2 2 = getr (ms_regs ms) 2)
    by exact (cl_cs (ms_regs ms) regs2 2 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
  rewrite E2.
  split; [exact Hsp4|].
  split; [exact (cl_cs (ms_regs ms) regs2 3 _ HPR ltac:(unfold acallee_saved; lia) Q3)|].
  split; [exact (cl_cs (ms_regs ms) regs2 4 _ HPR ltac:(unfold acallee_saved; lia) Q4)|].
  split; [exact (cl_cs (ms_regs ms) regs2 8 _ HPR ltac:(unfold acallee_saved; lia) Q8)|].
  split; [exact (cl_cs (ms_regs ms) regs2 9 _ HPR ltac:(unfold acallee_saved; lia) Q9)|].
  split; [exact (cl_cs (ms_regs ms) regs2 19 _ HPR ltac:(unfold acallee_saved; lia) Q19)|].
  split; [exact (cl_cs (ms_regs ms) regs2 18 _ HPR ltac:(unfold acallee_saved; lia) Q18)|].
  split; [exact (cl_cs (ms_regs ms) regs2 20 _ HPR ltac:(unfold acallee_saved; lia) Q20)|].
  exact (cl_cs (ms_regs ms) regs2 27 _ HPR ltac:(unfold acallee_saved; lia) Q27). }
split; [exact I|].
split.
{ split; [exact Hop|]. split; [exact Hop2|].
  split; [exact (cl_frm_keep B MT XM_LIB RLO RHI tfib_K LAWS cx nb fr len ly3 S3 W (ms_mem ms) md4 k W2 mem2 _ _
    (fun _ => False) h n dsh_rec HC4 Hbody4 HKT (fun a Ha => match Ha with end) Hfrm4)|].
  split; [split; [|split; [|split]]; apply VK; try lia; apply (hb_val_ext W mem3 (ms_mem ms) _ _ _ Hpt); assumption|].
  split; [split; apply VK; try lia; apply (hb_val_ext W mem3 (ms_mem ms) _ _ _ Hpt); assumption|].
  split; [exact Hlen | exact Hnb]. }
split.
{ destruct Hsp0 as (P1 & P2). split; apply VK; try lia; apply (hb_val_ext W mem3 (ms_mem ms) _ _ _ Hpt); assumption. }
apply (cl_body_call B MT XM_LIB RLO RHI tfib_K LAWS AIL KCAN cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) md4 k
  ly2 S2 W2 mem2 md2 k _ _ (fun _ => False) [] Hbody4 HC4 HC2 HKT).
- unfold CheckTable.TCHECK_TABLE_STK, ESTACK, MFRAME, LLVMF_STK in *. lia.
- lia.
- intros a [].
- intros a [].
- apply Forall_nil.
- exact HPerm.
- exact BTOBS.
Qed.
End h.
End f.
End d.
