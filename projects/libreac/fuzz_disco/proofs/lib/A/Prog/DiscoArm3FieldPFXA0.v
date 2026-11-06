(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module names changed; 1640 of its 1679 lines of code are new or changed and 6 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC81 YC45 YC88 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoRo DiscoArm3 DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs DiscoArm3FieldCall DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacHuntRole ReacHuntPin.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c disco_json_text disco_json_reader_model reac_disco_table_json_c reac_disco_table_age_c
slot_ser_defs slot_ser_Pq slot_ser_tokb jtok_is_c disco_jscalar_model disco_json_lemmas printf_facts_c slot_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition pfxa_acs : list YP09.chunk :=
  [YP09.mkChunk 392 (CVal 8 (SOff AT_F 240)); YP09.mkChunk 408 (CVal 8 (SLit 0))].
Definition pfxa_fcs (r : Z) : list YP09.chunk :=
  [YP09.mkChunk 1664 (CVal 4 (SLit 0)); YP09.mkChunk 2168 (CVal 4 (SLit r))].
Definition pfxa_narrow (l : smem) : smem :=
  match l with
  | [r0; r1; r2; r3; r4; r5] =>
      [set_window r0 0 0; set_window r1 0 0; set_window r2 1664 1668; set_window r3 0 0; set_window r4 0 0;
       set_window r5 0 0]
  | _ => l
  end.

Lemma pfxa_sw_sub : forall r a b, (b <= a \/ (YP09.r_wlo r <= a /\ b <= YP09.r_whi r)) -> subregion (set_window r a b) r.
Proof.
intros r a b H. unfold subregion, set_window.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact H | intros c Hc; exact Hc].
Qed.

Lemma pfxa_narrow_sub : forall shf acs fcs, submem (pfxa_narrow (d_kregions shf acs fcs)) (d_kregions shf acs fcs).
Proof.
intros shf acs fcs. unfold d_kregions, pfxa_narrow.
apply submem_keep; [apply pfxa_sw_sub; left; lia|].
apply submem_keep; [apply pfxa_sw_sub; left; lia|].
apply submem_keep; [apply pfxa_sw_sub; right; cbn [YP09.r_wlo YP09.r_whi]; unfold DFRAME_SIZE; lia|].
apply submem_keep; [apply pfxa_sw_sub; left; lia|].
apply submem_keep; [apply pfxa_sw_sub; left; lia|].
apply submem_keep; [apply pfxa_sw_sub; left; lia|].
apply submem_nil.
Qed.

Lemma pfxa_narrow0_sub : forall l, submem (map (fun r => set_window r 0 0) l) l.
Proof.
induction l as [|r l IH]; cbn [map]; [apply submem_nil|].
apply submem_keep; [apply pfxa_sw_sub; left; lia | exact IH].
Qed.

Lemma pfxa_nth_zle : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma pfxa_pfb : forall s : list Z, Forall (fun c => 0 <= c < 256) s ->
  map (fun b : byte => bv_unsigned b) (printf_facts_c.pf_bytes s) = s.
Proof.
induction s as [|c s IH]; intros F; [reflexivity|].
apply Forall_cons_iff in F as [Fc Fs]. unfold printf_facts_c.pf_bytes in *. cbn [map].
rewrite IH by exact Fs. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pfxa_st_ok_pi : forall (fq : YK11.FPState) E ss ms pc, st_ok (fx := fq) SEGS E (YP0l.setpc ss (BASE + pc)) ms ->
  st_ok_pi (fx := fq) SEGS VAL E (YP0l.setpc ss pc) ms.
Proof. intros fq E ss ms pc H. exact H. Qed.

Lemma pfxa_g8_val : forall (m : word -> option byte) a n z,
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (Z_to_le_bytes n z)) ->
  0 <= z < 2 ^ (8 * Z.of_nat n) -> val_mem SEGS m a n z.
Proof.
intros m a n z G Hz k Hk.
rewrite (garr8_mbyte SEGS m a _ k G) by (rewrite length_map, YK0h.length_Z_to_le_bytes; exact Hk).
f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, YK0h.length_Z_to_le_bytes; exact Hk).
rewrite map_nth. rewrite pfxa_nth_zle by exact Hk. rewrite Z_to_bv_bv_unsigned.
symmetry. apply le_byte_small; [exact Hz | exact Hk].
Qed.

Lemma pfxa_slot_vals : forall (m : word -> option byte) A buf vpad (t : disco_json_reader_model.tokv),
  length vpad = 4%nat -> disco_json_reader_model.tv_kind t <> 0 ->
  garr8 SEGS m A (map (fun b : byte => bv_unsigned b) (slot_ser_defs.slot24 buf vpad t)) ->
  0 <= buf + snd (fst t) < 2 ^ 64 -> 0 <= snd t < 2 ^ 64 -> 0 <= disco_json_reader_model.tv_kind t < 2 ^ 32 ->
  val_mem SEGS m A 8 (buf + snd (fst t)) /\ val_mem SEGS m (A + 8) 8 (snd t) /\
  val_mem SEGS m (A + 16) 4 (disco_json_reader_model.tv_kind t).
Proof.
intros m A buf vpad t Hv Hk G H1 H2 H3.
rewrite (slot_ser_Pq.slot24_split buf vpad t Hk) in G.
rewrite !map_app in G.
apply garr8_app in G as [G _]. apply garr8_app in G as [G1 G23]. apply garr8_app in G23 as [G2 G3].
rewrite !length_map, !Mem.length_le8 in G2. rewrite !length_map, !Mem.length_le8 in G3.
unfold Mem.le8, word_to_le_bytes in G1, G2. unfold Mem.le4 in G3.
rewrite unsigned_lit_small in G1 by lia. rewrite unsigned_lit_small in G2 by lia.
rewrite unsigned_lit_small in G3 by lia.
change (8 * Z.of_nat 8) with 64 in *.
split; [|split].
- apply pfxa_g8_val; [exact G1 | change (8 * Z.of_nat 8) with 64; lia].
- apply pfxa_g8_val; [exact G2 | change (8 * Z.of_nat 8) with 64; lia].
- replace (A + Z.of_nat 8 + Z.of_nat 8) with (A + 16) in G3 by lia.
  apply pfxa_g8_val; [exact G3 | change (8 * Z.of_nat 4) with 32; lia].
Qed.

Lemma pfxa_slot01 : forall (m : word -> option byte) A buf vpad (os : list disco_json_reader_model.jobj),
  length vpad = 4%nat -> Forall (fun o : disco_json_reader_model.jobj => length o = 6%nat) os -> (0 < length os)%nat ->
  garr8 SEGS m A (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)) ->
  garr8 SEGS m (A + 24) (map (fun b : byte => bv_unsigned b)
    (slot_ser_defs.slot24 buf vpad (nth 1 (nth 0 os []) disco_json_reader_model.tok_none))).
Proof.
intros m A buf vpad os Hv H6 Hl G. destruct os as [|o os']; [cbn in Hl; lia|].
apply Forall_cons_iff in H6 as [Ho _].
destruct o as [|t0 [|t1 o']]; cbn [length] in Ho; try discriminate Ho.
unfold slot_ser_defs.objs_bytes, slot_ser_defs.obj_bytes in G. cbn [map concat] in G.
rewrite !map_app in G.
apply garr8_app in G as [G _]. apply garr8_app in G as [_ G]. apply garr8_app in G as [G _].
rewrite length_map, (slot_ser_Pq.slot24_len buf vpad t0 Hv) in G. cbn [nth]. exact G.
Qed.

Lemma pfxa_slack : forall H (m : word -> option byte) x (l : list Z) n,
  garr8 SEGS (mrestrict H m) x l ->
  (forall j, 0 <= j < Z.of_nat n -> aview SEGS H m (x + Z.of_nat (length l) + j) <> None) ->
  exists sl : list byte, length sl = n /\
    garr8 SEGS (mrestrict H m) x (l ++ map (fun b : byte => bv_unsigned b) sl).
Proof.
intros H m x l n G. induction n as [|n IH]; intros Hv.
- exists []. split; [reflexivity|]. rewrite app_nil_r. exact G.
- destruct IH as (sl & Hl & G'); [intros j Hj; apply Hv; lia|].
  destruct (aview SEGS H m (x + Z.of_nat (length l) + Z.of_nat n)) as [v|] eqn:Ev;
    [|exfalso; exact (Hv (Z.of_nat n) ltac:(lia) Ev)].
  destruct (val_mem1_of_aview SEGS H m _ v Ev) as [Vm Vr].
  exists (sl ++ [Z_to_bv 8 v]). split; [rewrite length_app, Hl; cbn [length]; lia|].
  rewrite map_app, app_assoc. cbn [map].
  replace (bv_unsigned (Z_to_bv 8 v)) with v
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite Z.mod_small; lia).
  apply (garr8_app1 SEGS _ _ x _ v G'); [| exact Vr | intros a _; reflexivity].
  rewrite length_app, length_map, Hl.
  replace (x + Z.of_nat (length l + n)) with (x + Z.of_nat (length l) + Z.of_nat n) by lia. exact Vm.
Qed.

Lemma pfxa_tok_ra : forall (cx : dcx) (W : world SEGS) m, d_shadow cx dsh_ser2 W m -> d_FB cx mod 8 = 0 ->
  0 <= d_FB cx -> range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + 264) 20.
Proof.
intros cx W m HSH H8 H0 x Hx. exists 0. split; [|left; reflexivity].
assert (Hq : (x - d_FB cx) / 8 = 33 \/ (x - d_FB cx) / 8 = 34 \/ (x - d_FB cx) / 8 = 35) by lia.
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (shadow_addr (d_FB cx) + (x - d_FB cx) / 8) by (unfold shadow_addr; lia).
rewrite HSH by (unfold DFRAME_SH; lia).
destruct Hq as [Hq | [Hq | Hq]]; rewrite Hq; vm_compute; reflexivity.
Qed.

Lemma pfxa_tok_hull : forall (cx : dcx) (W : world SEGS) m,
  (forall i, 0 <= i < 512 -> apresent (w_H W) m (shadow_addr (d_FB cx) + i)) ->
  d_FB cx mod 32 = 0 -> 0 <= d_FB cx ->
  shadow_hull_vis (aview SEGS (w_H W) m) (d_FB cx + 264) 20.
Proof.
intros cx W m HP H32 H0 s Hs.
replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
apply aview_some_of_apresent. apply HP. unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.

Lemma pfxa_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma pfxa_dE : forall (cx : dcx) E j ws, d_E cx E -> (530 <= j)%nat -> d_E cx (havoc E j ws).
Proof.
intros cx E j ws (H1 & H32 & HI & H60 & H516 & H529) Hj.
split; [|split; [|split; [|split; [|split]]]].
- intros nn r Hr. pose proof (bv_unsigned_in_range 5 r) as Hb. change (bv_modulus 5) with 32 in Hb.
  rewrite ew_havoc_old by lia. exact (H1 nn r Hr).
- rewrite ew_havoc_old by lia. exact H32.
- apply img_env_havoc_hi; [exact HI | unfold A_LIM; lia].
- rewrite ew_havoc_old by (unfold AT_A; lia). exact H60.
- rewrite ew_havoc_old by (unfold AT_F; lia). exact H516.
- rewrite ew_havoc_old by (unfold AT_SH; lia). exact H529.
Qed.

Lemma pfxa_regs2 : forall (cx : dcx) (E : env) (R : bvmap 5 word),
  img_env VAL A_LIM E -> getr R 1 = Z_to_bv 64 (BASE + 8104) ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs))) (SLit 0 :: SOff A_TEXT 8104 :: atom_regs 532 30) R.
Proof.
intros cx E R HEI H1.
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                             | rewrite H1; symmetry; exact (codeptr_val _ 8104 HEId) ]).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.

Lemma pfxa_heap : forall ly S (W : world SEGS) m md p n a k,
  AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> p <= a -> a + k <= p + req_size n -> 0 <= k ->
  amem_range a k /\ range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a k /\
  (0 < k -> shadow_hull_vis (aview SEGS (w_H W) m) a k) /\ 4096 <= p /\ p + req_size n <= alloc_ceiling.
Proof.
intros ly S W m md p n a k HAR Hin H1 H2 Hk.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (HbSh & HbHull).
split; [exact (amem_range_sub_app p (req_size n) a k Hbapp Hbceil H1 H2 Hk)|].
split; [exact (block_shadow_range _ _ p (req_size n) a k HbSh H1 H2)|].
split; [|lia].
intros Hk0 s Hs. apply HbHull.
pose proof (YCbq.shadow_mono p a H1) as S1.
pose proof (YCbq.shadow_mono (a + k - 1) (p + req_size n - 1) ltac:(lia)) as S2.
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) S1) as D1.
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) S2) as D2. lia.
Qed.

Theorem a3f_pfxa_0 : seg_pfa_p_spec B MT XM_LIB RLO RHI tfib_K 0.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs.
unfold f_pfx, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R14) & (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED).
pose proof HSLOTS as (Hpc & H368 & H336).
pose proof HTAB as ((removed & Hage & Hpost) & HOT).
pose proof Hpost as (LT1 & _ & _ & _ & _ & _ & TOK1 & _).
destruct (a3f_count T1 now count os LT1 TOK1 Hnow HJR) as (Ecnt & Hc8 & Los & H6 & Hinb & Hg33 & Hlen).
assert (Hrole : disco_table_c.role_of_e T1 0 = 0 \/ disco_table_c.role_of_e T1 0 = 1 \/
  disco_table_c.role_of_e T1 0 = 2) by (pose proof TOK1 as (_ & T2 & _); apply T2; lia).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HBASE | split; [exact HJ | exact HFRS]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF0 & GFc & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HdE & HREG & HFLAG & H216 & H152).
pose proof HdE as (HER & HE32 & HEI0 & HEA & HEF & HESH).
assert (HA64 : 0 <= d_A cx < 2 ^ 64) by lia.
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44) by lia.
assert (HFU : bv_unsigned (ew E AT_F) = d_FB cx)
  by (rewrite HEF; unfold w64; apply unsigned_lit_small; lia).
assert (HEI : img_env VAL A_LIM (d_env cx E (a3f_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
assert (V1664 : val_mem SEGS (rd W mem3) (d_FB cx + 1664) 4 0).
{ assert (EU : a3f_used 0 = map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 32)) by (vm_compute; reflexivity).
  pose proof HUSED as HU0. rewrite EU in HU0.
  pose proof (ReacHuntRole.hunt_val4 SEGS (rd W mem3) (d_obj cx OUSED) _ 0 HU0 ltac:(lia)
    ltac:(rewrite repeat_length; lia)) as V.
  replace (disco_table_c.u_at (repeat (Z_to_bv 8 0) 32) 0 4) with 0 in V by (vm_compute; reflexivity).
  unfold d_obj, dobj_off in V. rewrite Z.add_0_r in V. exact V. }
assert (V2168 : val_mem SEGS (rd W mem3) (d_FB cx + 2168) 4 (disco_table_c.role_of_e T1 0)).
{ rewrite <- (a3f_role_u T1 0) by lia.
  pose proof (ReacHuntRole.hunt_val4 SEGS (rd W mem3) (d_obj cx OT) T1 (48 * 0 + 8) HOT ltac:(lia)
    ltac:(rewrite LT1; lia)) as V.
  unfold d_obj, dobj_off in V. replace (d_FB cx + 2160 + (48 * 0 + 8)) with (d_FB cx + 2168) in V by lia. exact V. }
destruct Hrole as [Er | [Er | Er]]; rewrite Er in V2168.
{
pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PFX_OFF (a3f_sr 0) (a3f_vals regs)
  pfxa_acs (pfxa_fcs 0) [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (a3f_regs_ok cx E 0 regs HdE HA64 ltac:(rewrite Z.add_0_r; exact Rsp) R8 R9 R18 R20 R25)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (a3f_vals regs) [] [] HCTX HdE I I)) as HSEED.
match type of HSEED with ?Q -> _ => assert (HACS : Q) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (chunk_ok_val _ _ _ _ _ _ _ (d_obj cx OO + 144 * 0)).
    + cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
      unfold d_obj, dobj_off. f_equal. lia.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold d_obj, dobj_off. lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H392.
  - eapply (chunk_ok_val _ _ _ _ _ _ _ 0).
    + reflexivity.
    + lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H408. }
specialize (HSEED HACS). clear HACS.
match type of HSEED with ?Q -> _ => assert (HFCS : Q) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. exact V1664.
  - eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. exact V2168. }
specialize (HSEED HFCS). clear HFCS.
pose proof (HSEED (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
clear HSEED. unfold ss_d in HS0. rewrite app_nil_r in HS0.
pose proof (st_ok_pi_submem _ _ _ _ HS0 (pfxa_narrow_sub dsh_ser2 pfxa_acs (pfxa_fcs 0)) ltac:(vm_compute; reflexivity))
  as HS1.
clear HS0. cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS1.
pose proof (ast_ok_pi_set_reg_fp _ _ _ (14%bv : bv 5) (SOff AT_F 2160) HS1 eq_refl) as HS2.
clear HS1.
assert (HS : st_ok_pi (fx := fq) SEGS VAL (d_env cx E (a3f_vals regs))
  (mkSS PFX_OFF (sr_set (a3f_sr 0) (14%bv : bv 5) (SOff AT_F 2160))
     (pfxa_narrow (d_kregions dsh_ser2 pfxa_acs (pfxa_fcs 0))) None (d_facts [] []))
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PFX_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ apply HS2. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  rewrite restrict_mkst_fx. cbn [ms_regs YK11.mkst]. unfold d_obj, dobj_off in R14. rewrite R14. reflexivity. }
clear HS2.
norm_ss HS.
rewrite Ec. unfold cfg_at. change (w64 (BASE + PFX_OFF)) with (Z_to_bv 64 (BASE + PFX_OFF)).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (a3f_vals regs)) (rd W (ms_mem (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PFX_OFF)) mem3 (YK11.seg_rom SEGS))))) by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN HS HJ SHOK (0, 0).
1: { lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
       let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end.
     apply awr_ok_cons_ro; [cbn; lia|].
     apply awr_ok_cons_ro; [cbn; lia|].
     eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat (d_FB cx)).
     - reflexivity.
     - rewrite d_env_old by (cbv; lia). exact HFU.
     - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply (HAWRF a). unfold DFRAME_SIZE. lia.
     - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS.
rewrite pa_sigma_jtok_is. rewrite pa_sigma_jtok_is in HS.
pose proof (pfxa_st_ok_pi fq _ _ _ AF_jtok_is HS) as HSpi.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
clear HS.
set (R := ms_regs ms) in *.
set (memc := ms_mem ms) in *.
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
rewrite (a3f_env_reg cx E regs 3%bv 534 eq_refl) in Q3.
rewrite (a3f_env_reg cx E regs 4%bv 535 eq_refl) in Q4.
rewrite (a3f_env_reg cx E regs 26%bv 557 eq_refl) in Q26.
rewrite (d_env_old cx E (a3f_vals regs) 60) in Q2, Q9 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 2) in Q8 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 32) in Q18 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 516) in Q10, Q24 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 252) in Q12 by (cbv; lia).
change (ew E 516) with (ew E AT_F) in Q10, Q24. rewrite HFU in Q10, Q24.
change (ew E 60) with (ew E AT_A) in Q2, Q9. rewrite HEA in Q2, Q9.
rewrite HE32 in Q18.
rewrite (HER 2%nat 2%bv eq_refl) in Q8.
rewrite (img_env_atomP E 252 HEI0 ltac:(cbv; lia)) in Q12.
assert (SpR : spZ R = d_A cx) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (Htk : TJTOK_IS_STK = 8240) by reflexivity.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (d_FB cx + 1664 <= a < d_FB cx + 1668) ->
  aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem3 a).
{ apply (jt_kept_frame _ _ (w_H W) mem3 memc (d_FB cx + 1664) (d_FB cx + 1668) HFr).
  intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val];
     first [left; lia | right; rewrite d_env_old by (cbv; lia); change 516%nat with AT_F; rewrite HFU; lia] | ]).
  destruct Hr. }
assert (KV : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat nb -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668)) ->
  val_mem SEGS (rd W mem3) a nb v -> val_mem SEGS (rd W memc) a nb v).
{ intros a nb v Ha Hb Hx Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memc); [|exact Hv].
  intros kk Hkk. apply KC; [lia | apply Hx; lia]. }
assert (KG : forall a L, 0 <= a -> a + Z.of_nat (length L) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length L) -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668)) ->
  garr8 SEGS (rd W mem3) a L -> garr8 SEGS (rd W memc) a L).
{ intros a L Ha Hb Hx Hv. eapply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 memc); [|exact Hv].
  intros x Hx'. apply KC; [lia | apply Hx; lia]. }
assert (H216c : val_mem SEGS (rd W memc) (d_A cx + 216) 8 h) by (apply KV; [lia | lia | intros x Hx; lia | exact H216]).
assert (H152c : val_mem SEGS (rd W memc) (d_A cx + 152) 8 (h + 440))
  by (apply KV; [lia | lia | intros x Hx; lia | exact H152]).
assert (HCTXc : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W memc mdc k) by exact (conj HBASE (conj HJ HFRS)).
pose proof (DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W mdc k (d_env cx E (a3f_vals regs)) _ ms HCTXc
  (d_E_env cx E (a3f_vals regs) HdE) (d_env_fl cx E (a3f_vals regs)) HSpi ltac:(vm_compute; reflexivity)
  H216c H152c) as (HFRMc & HSHDc).
assert (HBODYc : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W memc).
{ apply (d_body_rt B cx h n n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W mem3 memc (d_A cx) (d_A cx)
    (fun a => d_FB cx + 1664 <= a < d_FB cx + 1668) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right. unfold d_rdset, d_objr. pose proof HGEO as (_ & _ & _ & _ & _ & _ & Gh & Gp).
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Gh, Gp. unfold slot_inv.HUNT_SIZE in Gh.
    intros [Hx | [Hx | [Hx | [Hx | [Hx | [Hx | [(Hro & _ & _) | Hcn]]]]]]].
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold slot_inv.HUNT_SIZE in Hx. lia.
    + destruct Hx as (Hc & Hx). specialize (Gp Hc). lia.
    + exact (off_img_not_img (d_FB cx) 4096 a GFoff ltac:(lia) (in_roP_img a Hro)).
    + exact (off_img_not_img (d_FB cx) 4096 a GFoff ltac:(lia) (proj2 (proj2 HCAN) a Hcn)).
  - intros a Ha Hna. exact (KC a Ha Hna).
  - intros a _ Hp. eapply apresent_grows; [exact HG | exact Hp].
  - exact HFRMc.
  - exact HSHDc.
  - lia. }
pose proof HBODYc as (Tc & Gc & Lkc & Hc & _ & _ & _ & _ & _ & HIMGc & _).
pose proof (proj1 HJ) as HARc.
pose proof (DCRO LAWS (conj DRO (conj GM (HV))) ly3 S3 W memc mdc HARc HIMGc) as (_ & _ & _ & HSTRS & _).
pose proof (a3f_rolestr W memc 0 ltac:(lia) HSTRS) as HKEY.
change (a3f_roleobj 0) with 11%nat in HKEY.
set (txt := disco_json_text.rolename 0) in *.
destruct HKEY as ((KF & KG0 & Kx0 & Kx63 & Kx32 & KAM & KRA & KSH & KTL & KIMG) & KROM).
set (xk := VAL (A_OBJ 11)) in *.
destruct (pfxa_slack (w_H W) memc xk (txt ++ [0]) (Z.to_nat ((- (xk + Z.of_nat (length txt) + 1)) mod 8)) KG0)
  as (sl & Hsl & KG1).
{ intros j Hj. rewrite length_app. cbn [length]. apply KTL. lia. }
assert (KG2 : garr8 SEGS (rd W memc) xk
  (map (fun b : byte => bv_unsigned b) (printf_facts_c.pf_bytes txt ++ Z_to_bv 8 0 :: sl))).
{ rewrite map_app. cbn [map]. rewrite pfxa_pfb by (eapply Forall_impl; [|exact KF]; intros cc Hcc; cbv beta in Hcc; lia).
  change (bv_unsigned (Z_to_bv 8 0)) with 0. rewrite <- app_assoc in KG1. exact KG1. }
assert (HTL : length (printf_facts_c.pf_bytes txt) = length txt) by (unfold printf_facts_c.pf_bytes; apply length_map).
set (X := a3_text T1 now) in *.
assert (LXeq : Z.of_nat (length (a3_text T1 now)) = Z.of_nat (length X)) by reflexivity.
set (t := nth 1 (nth 0 os []) disco_json_reader_model.tok_none).
pose proof (a3f_obj T1 now count os 0 LT1 TOK1 Hnow HJR ltac:(lia)) as HOB0. cbv zeta in HOB0.
destruct HOB0 as (_ & HRT & _).
change (Z.to_nat 0) with 0%nat in HRT.
change (disco_json_text.e_role (reac_disco_table_json_c.tj_entry T1 0)) with (disco_table_c.role_of_e T1 0) in HRT.
rewrite Er in HRT. fold X t txt in HRT.
pose proof HRT as HRT'. unfold disco_json_reader_model.jtok_is in HRT'.
apply andb_prop in HRT' as [HRT1 HRT3]. apply andb_prop in HRT1 as [HRk HRn].
apply Z.eqb_eq in HRk, HRn. apply disco_json_lemmas.lzeqb_true in HRT3.
assert (Hlos : (0 < length os)%nat) by lia.
assert (Ho6 : length (nth 0 os []) = 6%nat) by (apply (proj1 (Forall_forall _ _) H6); apply nth_In; lia).
assert (Htin : In t (nth 0 os [])) by (unfold t; apply nth_In; rewrite Ho6; lia).
pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Hinb (nth 0 os []) (nth_In _ _ Hlos)) t Htin) as Htb.
unfold slot_ser_tokb.tok_inb, disco_jscalar_model.jlen in Htb.
destruct Htb as [Hk0 | (Hs0 & Hl0 & Hsl0)]; [fold t in Hk0; lia|].
fold t in Hs0, Hl0, Hsl0.
pose proof HBUF as (HBr & HBG). unfold a3_r in HBr. fold X in HBr, HBG.
assert (HinB : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ pose proof HBLK as (HPerm0 & _). apply (Permutation_in _ (Permutation_sym HPerm0)).
  apply in_or_app. left. left. reflexivity. }
assert (Hrq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W memc mdc buf _ DFRAME_CLASS (c_fpos cx) HARc HinB HFin3) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. rewrite EFA3, Hrq in HdBF.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HdBF.
assert (HTXL : Z.of_nat (length txt) = snd t) by lia.
destruct (pfxa_heap ly3 S3 W memc mdc buf _ (buf + snd (fst t)) (Z.of_nat (length txt)) HARc HinB ltac:(lia)
  ltac:(rewrite Hrq; lia) ltac:(lia)) as (PAM & PRA & PSH & Pb4096 & Pbceil).
rewrite Hrq in Pbceil.
assert (HBGc : garr8 SEGS (rd W memc) buf (X ++ [0])).
{ apply KG; [lia | rewrite length_app; cbn [length]; lia | intros x Hx; rewrite length_app in Hx; cbn [length] in Hx; lia | exact HBG]. }
assert (HPG : garr8 SEGS (rd W memc) (buf + snd (fst t))
  (map (fun b : byte => bv_unsigned b) (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)))).
{ rewrite pfxa_pfb.
  2: { rewrite HRT3. eapply Forall_impl; [|exact KF]; intros cc Hcc; cbv beta in Hcc; lia. }
  pose proof (garr8_sub_x SEGS _ _ _ (Z.to_nat (snd (fst t))) (Z.to_nat (snd t)) HBGc
    ltac:(rewrite length_app; cbn [length]; lia)) as Gsub.
  rewrite Z2Nat.id in Gsub by lia.
  unfold disco_json_reader_model.tv_text.
  rewrite skipn_app, firstn_app in Gsub.
  replace (Z.to_nat (snd t) - length (skipn (Z.to_nat (snd (fst t))) X))%nat with 0%nat in Gsub
    by (rewrite length_skipn; lia).
  cbn [firstn] in Gsub. rewrite app_nil_r in Gsub. exact Gsub. }
assert (HOOc : garr8 SEGS (rd W memc) (d_obj cx OO)
  (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))).
{ assert (LOSn : (length (slot_ser_defs.objs_bytes buf vpad os) = 144 * Z.to_nat count)%nat)
    by (rewrite (slot_ser_Pq.objs_len buf vpad os HVP H6); f_equal; exact Los).
  assert (LOO : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)))
    = 144 * count) by (rewrite length_map, LOSn; lia).
  apply KG; [unfold d_obj, dobj_off; lia | rewrite LOO; unfold d_obj, dobj_off; lia |
    intros x Hx; rewrite LOO in Hx; unfold d_obj, dobj_off in Hx; lia | exact HOO]. }
pose proof (pfxa_slot01 _ _ buf vpad os HVP H6 Hlos HOOc) as HSL. fold t in HSL.
destruct (pfxa_slot_vals _ _ buf vpad t HVP ltac:(lia) HSL ltac:(lia) ltac:(lia) ltac:(lia)) as (Mvp & Mvn & Mvk).
unfold d_obj, dobj_off in Mvp, Mvn, Mvk.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat
  (YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 1664 1668
     (YP09.mkChunk 1664 (CVal 4 (SLit 1)) :: dfhdr_chunks ++ [YP09.mkChunk 2168 (CVal 4 (SLit 0))]))
  HSpi eq_refl) as HR516.
assert (HG1664 : garr8 SEGS (rd W memc) (d_obj cx OUSED) [1; 0; 0; 0]).
{ pose proof (Forall_inv (proj2 (proj2 (proj2 HR516)))) as HC1.
  cbn [YP09.r_base base_val] in HC1. rewrite d_env_old in HC1 by (cbv; lia).
  change 516%nat with AT_F in HC1. rewrite HFU in HC1.
  pose proof (ReacHuntPin.pin_garr8_le4 SEGS (d_env cx E (a3f_vals regs)) (rd W memc) (d_FB cx) 1664
    (SLit 1) (Z_to_bv 64 1) HC1 eq_refl) as HG0.
  replace (map (fun b : byte => bv_unsigned b) (Mem.le4 (Z_to_bv 64 1))) with [1; 0; 0; 0] in HG0
    by (vm_compute; reflexivity).
  unfold d_obj, dobj_off. exact HG0. }
assert (HMCin : In (McConsts.MC_CONSTS_LO, 32) disco_ro_ranges).
{ unfold disco_ro_ranges. apply in_or_app. right. cbn. repeat (first [left; reflexivity | right]). }
replace (d_FB cx + 240 + 24) with (d_FB cx + 264) in Mvp, Mvn, Mvk by lia.
assert (HMCro : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a).
{ intros a Ha. apply (disco_ro_in_ro _ _ a (in_or_app _ _ _ (or_introl HMCin))).
  unfold McConsts.MC_CONSTS_LO, McConsts.MC_CONSTS_HI in Ha |- *. lia. }
assert (HMCun : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. apply (disco_ro_unowned_at B _ _ DRO HMCin a).
  unfold McConsts.MC_CONSTS_LO, McConsts.MC_CONSTS_HI in Ha |- *. lia. }
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W memc mdc k HCTXc)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpresc & GSHc & GSTKc & _ & _ & _ & _).
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
pose proof (pa_img_range xk (KIMG xk ltac:(lia))) as XR. unfold IMG_LO, IMG_TOP in XR.
assert (Ltxt : (length txt <= 7)%nat) by (unfold txt; cbv; lia).
assert (Lsl : (length sl <= 7)%nat) by (rewrite Hsl; pose proof (Z.mod_pos_bound (- (xk + Z.of_nat (length txt) + 1)) 8 ltac:(lia)); lia).
eapply SRr_bind; [apply (aj_jtok_at B LAWS TJTOK fq W R memc LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 mdc k (d_A cx - d_S cx) (d_FB cx + 264) xk 1 1
    (buf + snd (fst t)) (snd t) (printf_facts_c.pf_bytes txt) sl
    (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)) HJ) |].
- rewrite SpR. lia.
- lia.
- lia.
- rewrite Htk. unfold LLVMF_STK. lia.
- rewrite Q3. exact Rgp.
- rewrite Q4. exact Rtp.
- rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
- unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
- exact HIMGc.
- exact (mc_cv_ok B W memc HMCro HMCun HIMGc).
- exact Q10.
- exact Q11.
- exact Q12.
- lia.
- lia.
- lia.
- lia.
- lia.
- exact Mvp.
- exact Mvn.
- change (1 mod 2 ^ 32) with 1. rewrite <- HRk. exact Mvk.
- lia.
- lia.
- apply (amem_range_sub_app (d_FB cx) 4096); [exact GFapp | lia | lia | lia | lia].
- exact (pfxa_tok_ra cx W memc HSHDc ltac:(lia) ltac:(lia)).
- exact (pfxa_tok_hull cx W memc GSHc GF32 ltac:(lia)).
- left. rewrite SpR, Htk. lia.
- exact (slot_ser_Pq.pf_no_zero txt KF).
- exact KG2.
- rewrite HTL, Hsl. rewrite Z2Nat.id; [lia | apply Z.mod_pos_bound; lia].
- exact Kx0.
- rewrite HTL. lia.
- rewrite HTL. lia.
- rewrite HTL. replace (Z.of_nat (length txt + 1)) with (Z.of_nat (length txt) + 1) by lia. exact KAM.
- rewrite HTL. replace (Z.of_nat (length txt + 1)) with (Z.of_nat (length txt) + 1) by lia. exact KRA.
- rewrite HTL. replace (Z.of_nat (length txt + 1)) with (Z.of_nat (length txt) + 1) by lia. exact KSH.
- left. rewrite SpR, Htk, HTL. lia.
- intros _ _.
  assert (LP : length (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)) =
    length (printf_facts_c.pf_bytes txt)) by (rewrite HRT3; reflexivity).
  rewrite LP, HTL.
  split; [reflexivity|]. split; [exact HPG|]. split; [lia|]. split; [lia|].
  split; [exact PAM|]. split; [exact PRA|]. split; [exact PSH|].
  left. rewrite SpR, Htk. lia.
- intros W2 c2 HW2 (fq2 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hcsr2 & HJ4 & HJc & HP4 & HPerm & HKeep & Hres).
  assert (HXb : Forall (fun cc => 0 <= cc < 256) X) by (eapply Forall_impl; [|exact Hg33]; intros cc Hcc; cbv beta in Hcc; lia).
  pose proof (proj2 (slot_ser_Pq.jt_iff X t 1 txt HXb KF ltac:(lia)) HRT) as HM. rewrite HRk in HM.
  assert (R10 : getr regs4 10 = w64 1) by (destruct Hres as [(_ & H10) | (Hn10 & _)]; [exact H10 | contradiction]).
  rewrite SpR, Htk in HKeep.
  pose proof HJc as (_ & _ & _ & _ & _ & HfrC & _).
  assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFRS).
  assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR4)).
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 k HCTX4)
    as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
  destruct HFRMc as (E2 & HdE2 & HREG2 & HFLAG2 & _ & _).
  pose proof HdE2 as (HER2 & HE322 & HEI2 & HEA2 & HEF2 & HESH2).
  assert (HEId2 : img_env VAL A_LIM (d_env cx E2 (map (getr R) (tl all_regs))))
    by (apply img_env_havoc_hi; [exact HEI2 | unfold AT_FL, A_LIM; lia]).
  pose proof (DSEAT LAWS PAL fq2 cx dsh_ser2 ly3 S3 W R memc mdc k E2 AF_jtok_is
    (SLit 0 :: SOff A_TEXT 8104 :: atom_regs 532 30) (map (getr R) (tl all_regs)) [] [] [] (d_facts [] [])
    HCTXc HdE2 HREG2 HFLAG2 (pfxa_regs2 cx E2 R HEI2 Q1)
    (DFACTS LAWS cx ly3 S3 W memc mdc k E2 (map (getr R) (tl all_regs)) [] [] HCTXc HdE2 I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HSC.
  jafter_call_keep_hi HSC 562%nat regs4 (mrestrict (w_H W2) mem4) HP4 [0;1;2;3]%nat HS2.
  match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
  { cbn [ms_mem restrict YK11.mkst]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (d_S cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). rewrite (HER2 2%nat 2%bv eq_refl). reflexivity.
      + intros a Ha. apply HKeep; lia.
      + intros a Ha. lia.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (d_A cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite HEA2. unfold w64.
        apply unsigned_lit_small. lia.
      + intros a Ha. apply HKeep; lia.
      + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (d_FB cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite HEF2. unfold w64.
        apply unsigned_lit_small. lia.
      + intros a Ha. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. apply HKeep; lia.
      + intros a Ha. apply GFpres4. unfold DFRAME_SIZE in Ha. lia.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (shadow_addr (d_FB cx))).
      + rewrite d_env_old by (unfold AT_FL; lia). change 529%nat with AT_SH. rewrite HESH2. unfold w64.
        apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia.
      + intros a Ha. apply HKeep; unfold shadow_addr, SHADOW_OFF in *; lia.
      + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
        apply GFsh4. lia. }
  specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
  assert (HE3 : d_E cx (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
    by (apply pfxa_dE; [apply d_E_env; exact HdE2 | lia]).
  assert (HFL3 : ew (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
    Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
    by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
  assert (HEI3 : img_env VAL A_LIM (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
    by (apply img_env_havoc_hi; [exact HEId2 | unfold A_LIM; lia]).
  pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 1 HS2 ltac:(cbn [ms_regs restrict YK11.mkst]; exact R10) eq_refl)
    as HS3.
  clear HS2.
  pose proof (st_ok_pi_submem _ _ _ _ HS3 (pfxa_narrow0_sub _) ltac:(vm_compute; reflexivity)) as HS4.
  clear HS3. cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS4. norm_ss HS4.
  rewrite Q1.
  pose proof HJ4 as HJ4c.
  clear HF HFr HG.
  pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq2) B LAWS).
  paj_run_to_shc RUNTOP HS4 HJ4 R1_OFF.
  + lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil.
  + assert (Emem : ms_mem ms0 = mem4).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hr & Hw).
      vm_compute in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia|]). destruct Hr. }
    pmkst HS4.
    prreg HS4 (2%bv : bv 5) F2. prreg HS4 (3%bv : bv 5) F3. prreg HS4 (4%bv : bv 5) F4. prreg HS4 (8%bv : bv 5) F8.
    prreg HS4 (9%bv : bv 5) F9. prreg HS4 (18%bv : bv 5) F18. prreg HS4 (20%bv : bv 5) F20.
    prreg HS4 (24%bv : bv 5) F24. prreg HS4 (25%bv : bv 5) F25. prreg HS4 (26%bv : bv 5) F26.
    assert (KV4 : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat nb -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668) /\ ~ (d_A cx - 8240 <= x < d_A cx)) ->
      val_mem SEGS (rd W mem3) a nb v -> val_mem SEGS (rd W2 mem4) a nb v).
    { intros a nb v Ha Hb Hx Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
      intros kk Hkk. destruct (Hx (a + kk) ltac:(lia)) as (Hx1 & Hx2).
      rewrite (HKeep (a + kk) ltac:(lia) Hx2). apply KC; [lia | exact Hx1]. }
    assert (KG4 : forall a L, 0 <= a -> a + Z.of_nat (length L) <= 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat (length L) -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668) /\ ~ (d_A cx - 8240 <= x < d_A cx)) ->
      garr8 SEGS (rd W mem3) a L -> garr8 SEGS (rd W2 mem4) a L).
    { intros a L Ha Hb Hx Hv. eapply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
      intros x Hx'. destruct (Hx x Hx') as (Hx1 & Hx2).
      rewrite (HKeep x ltac:(lia) Hx2). apply KC; [lia | exact Hx1]. }
    assert (H216f : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 216) 8 h)
      by (rewrite Emem; apply KV4; [lia | lia | intros x Hx; split; lia | exact H216]).
    assert (H152f : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 152) 8 (h + 440))
      by (rewrite Emem; apply KV4; [lia | lia | intros x Hx; split; lia | exact H152]).
    assert (HCTXf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 (ms_mem ms0)
      (with_vm_backing (m_vm_lazy md4) mat0 md4) k) by exact (conj HBASE (conj HJ4 HFR4)).
    pose proof (DLAND LAWS FFL fq2 cx h dsh_ser2 ly4 S4 W2 (with_vm_backing (m_vm_lazy md4) mat0 md4) k
      (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) _ ms0 HCTXf HE3 HFL3 HS4
      ltac:(vm_compute; reflexivity) H216f H152f) as (HFRMf & HSHDf).
    rewrite Emem in HFRMf, HSHDf, HJ4.
    pose proof (d_body_call_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W memc
      ly4 S4 W2 mem4 md4 k (d_A cx - 8240) (d_A cx) HBODYc (conj HBASE HJ4c) ltac:(unfold LLVMF_STK; lia) ltac:(lia)
      ltac:(intros a Ha Hna; exact (HKeep a Ha Hna)) HPerm HFRMf HSHDf) as HBODYf.
    assert (F2' : getr (ms_regs ms0) 2 = getr R 2)
      by (rewrite F2; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 1 ltac:(rewrite length_map; cbn; lia))).
    assert (F3' : getr (ms_regs ms0) 3 = getr R 3)
      by (rewrite F3; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 2 ltac:(rewrite length_map; cbn; lia))).
    assert (F4' : getr (ms_regs ms0) 4 = getr R 4)
      by (rewrite F4; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 3 ltac:(rewrite length_map; cbn; lia))).
    assert (F8' : getr (ms_regs ms0) 8 = getr R 8)
      by (rewrite F8; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 7 ltac:(rewrite length_map; cbn; lia))).
    assert (F9' : getr (ms_regs ms0) 9 = getr R 9)
      by (rewrite F9; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 8 ltac:(rewrite length_map; cbn; lia))).
    assert (F18' : getr (ms_regs ms0) 18 = getr R 18)
      by (rewrite F18; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 17 ltac:(rewrite length_map; cbn; lia))).
    assert (F20' : getr (ms_regs ms0) 20 = getr R 20)
      by (rewrite F20; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 19 ltac:(rewrite length_map; cbn; lia))).
    assert (F24' : getr (ms_regs ms0) 24 = getr R 24)
      by (rewrite F24; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 23 ltac:(rewrite length_map; cbn; lia))).
    assert (F25' : getr (ms_regs ms0) 25 = getr R 25)
      by (rewrite F25; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 24 ltac:(rewrite length_map; cbn; lia))).
    assert (F26' : getr (ms_regs ms0) 26 = getr R 26)
      by (rewrite F26; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 25 ltac:(rewrite length_map; cbn; lia))).
    assert (HU1 : garr8 SEGS (rd W2 mem4) (d_obj cx OUSED) (a3f_used 1)).
    { assert (EU1 : a3f_used 1 = [1; 0; 0; 0] ++ skipn 4 (a3f_used 0)) by (vm_compute; reflexivity).
      rewrite EU1. apply garr8_app. split.
      - apply (garr8_aview_kept SEGS (w_H W) (w_H W2) memc mem4 (d_obj cx OUSED) [1;0;0;0]); [|exact HG1664].
        intros x Hx. cbn [length] in Hx. apply HKeep; unfold d_obj, dobj_off in *; lia.
      - cbn [length].
        assert (HT0 : garr8 SEGS (rd W mem3) (d_obj cx OUSED + 4) (skipn 4 (a3f_used 0))).
        { rewrite <- (firstn_skipn 4 (a3f_used 0)) in HUSED.
          apply garr8_app in HUSED as [_ HUt].
          replace (length (firstn 4 (a3f_used 0))) with 4%nat in HUt by (vm_compute; reflexivity).
          exact HUt. }
        apply KG4; [unfold d_obj, dobj_off; lia | | | exact HT0];
          replace (length (skipn 4 (a3f_used 0))) with 28%nat by (vm_compute; reflexivity);
          [|intros x Hx; split]; unfold d_obj, dobj_off in *; lia. }

    rewrite Emem.
    apply SRr_ret.
    unfold f_r1, a3f_st. split.
    { destruct HFROM as (HA3 & HW0 & HL0 & HEX). split; [exact HA3|].
      split; [eapply wle_trans; [exact HW0 | exact HW2]|]. split; [exact HL0 | exact HEX]. }
    unfold d_arm_at_pf, d_at.
    exists fq2, ly4, S4, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), k, acc.
    split; [unfold cfg_at, w64, R1_OFF; reflexivity|].
    split; [destruct Hcsr2 as [Hcs | Hcs]; [rewrite Hcs; assumption | exact Hcs]|]. split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|]. split; [exact Hk|].
    split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
    split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
    split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
    pose proof HSP1 as ((H232 & H344) & H224 & H248).
    split.
    { split; [unfold spZ; rewrite F2'; exact SpR|].
      split; [rewrite F3', Q3; exact Rgp|]. split; [rewrite F4', Q4; exact Rtp|].
      split; [rewrite F8', Q8; unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
      split; [rewrite F9'; exact Q9|]. split; [rewrite F18'; exact Q18|].
      split; [rewrite F20'; exact Q20|]. rewrite F25'; exact Q25. }
    split.
    { split; [rewrite F26', Q26; exact R26|]. rewrite F24', Q24. unfold w64, d_obj, dobj_off. f_equal. lia. }
    split.
    { split.
      { split; [split|split].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H232].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H344].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H224].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H248]. }
      split.
      { split; [exact (proj1 HTAB)|].
        apply KG4; [unfold d_obj, dobj_off; lia | | | exact HOT];
          rewrite length_map, LT1; [|intros x Hx; split]; unfold d_obj, dobj_off in *; lia. }
      split.
      { split; [exact HBr|].
        apply KG4; [lia | | | exact HBG]; rewrite length_app; cbn [length];
          [|intros x Hx; split]; lia. }
      split; [exact HJR|]. split; [exact HVP|].
      split.
      { assert (LOSn : (length (slot_ser_defs.objs_bytes buf vpad os) = 144 * Z.to_nat count)%nat)
          by (rewrite (slot_ser_Pq.objs_len buf vpad os HVP H6); f_equal; exact Los).
        assert (LOO : Z.of_nat (length (map (fun b : byte => bv_unsigned b)
          (slot_ser_defs.objs_bytes buf vpad os))) = 144 * count) by (rewrite length_map, LOSn; lia).
        apply KG4; [unfold d_obj, dobj_off; lia | rewrite LOO; unfold d_obj, dobj_off; lia |
          intros x Hx; rewrite LOO in Hx; unfold d_obj, dobj_off in Hx; split; lia | exact HOO]. }
      split.
      { split; [exact Hpc|].
        split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H368]|].
        apply KV4; [lia | lia | intros x Hx; split; lia | exact H336]. }
      split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H392]|].
      split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H408]|].
      exact HU1. }
    split.
    { split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H232]|].
      apply KV4; [lia | lia | intros x Hx; split; lia | exact H344]. }
    exact HBODYf.
}
{
pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PFX_OFF (a3f_sr 0) (a3f_vals regs)
  pfxa_acs (pfxa_fcs 1) [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (a3f_regs_ok cx E 0 regs HdE HA64 ltac:(rewrite Z.add_0_r; exact Rsp) R8 R9 R18 R20 R25)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (a3f_vals regs) [] [] HCTX HdE I I)) as HSEED.
match type of HSEED with ?Q -> _ => assert (HACS : Q) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (chunk_ok_val _ _ _ _ _ _ _ (d_obj cx OO + 144 * 0)).
    + cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
      unfold d_obj, dobj_off. f_equal. lia.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold d_obj, dobj_off. lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H392.
  - eapply (chunk_ok_val _ _ _ _ _ _ _ 0).
    + reflexivity.
    + lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H408. }
specialize (HSEED HACS). clear HACS.
match type of HSEED with ?Q -> _ => assert (HFCS : Q) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. exact V1664.
  - eapply (chunk_ok_val _ _ _ _ _ _ _ 1); [reflexivity | lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. exact V2168. }
specialize (HSEED HFCS). clear HFCS.
pose proof (HSEED (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
clear HSEED. unfold ss_d in HS0. rewrite app_nil_r in HS0.
pose proof (st_ok_pi_submem _ _ _ _ HS0 (pfxa_narrow_sub dsh_ser2 pfxa_acs (pfxa_fcs 1)) ltac:(vm_compute; reflexivity))
  as HS1.
clear HS0. cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS1.
pose proof (ast_ok_pi_set_reg_fp _ _ _ (14%bv : bv 5) (SOff AT_F 2160) HS1 eq_refl) as HS2.
clear HS1.
assert (HS : st_ok_pi (fx := fq) SEGS VAL (d_env cx E (a3f_vals regs))
  (mkSS PFX_OFF (sr_set (a3f_sr 0) (14%bv : bv 5) (SOff AT_F 2160))
     (pfxa_narrow (d_kregions dsh_ser2 pfxa_acs (pfxa_fcs 1))) None (d_facts [] []))
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PFX_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ apply HS2. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  rewrite restrict_mkst_fx. cbn [ms_regs YK11.mkst]. unfold d_obj, dobj_off in R14. rewrite R14. reflexivity. }
clear HS2.
norm_ss HS.
rewrite Ec. unfold cfg_at. change (w64 (BASE + PFX_OFF)) with (Z_to_bv 64 (BASE + PFX_OFF)).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (a3f_vals regs)) (rd W (ms_mem (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PFX_OFF)) mem3 (YK11.seg_rom SEGS))))) by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN HS HJ SHOK (0, 0).
1: { lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
       let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end.
     apply awr_ok_cons_ro; [cbn; lia|].
     apply awr_ok_cons_ro; [cbn; lia|].
     eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat (d_FB cx)).
     - reflexivity.
     - rewrite d_env_old by (cbv; lia). exact HFU.
     - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply (HAWRF a). unfold DFRAME_SIZE. lia.
     - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS.
rewrite pa_sigma_jtok_is. rewrite pa_sigma_jtok_is in HS.
pose proof (pfxa_st_ok_pi fq _ _ _ AF_jtok_is HS) as HSpi.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
clear HS.
set (R := ms_regs ms) in *.
set (memc := ms_mem ms) in *.
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
rewrite (a3f_env_reg cx E regs 3%bv 534 eq_refl) in Q3.
rewrite (a3f_env_reg cx E regs 4%bv 535 eq_refl) in Q4.
rewrite (a3f_env_reg cx E regs 26%bv 557 eq_refl) in Q26.
rewrite (d_env_old cx E (a3f_vals regs) 60) in Q2, Q9 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 2) in Q8 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 32) in Q18 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 516) in Q10, Q24 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 254) in Q12 by (cbv; lia).
change (ew E 516) with (ew E AT_F) in Q10, Q24. rewrite HFU in Q10, Q24.
change (ew E 60) with (ew E AT_A) in Q2, Q9. rewrite HEA in Q2, Q9.
rewrite HE32 in Q18.
rewrite (HER 2%nat 2%bv eq_refl) in Q8.
rewrite (img_env_atomP E 254 HEI0 ltac:(cbv; lia)) in Q12.
assert (SpR : spZ R = d_A cx) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (Htk : TJTOK_IS_STK = 8240) by reflexivity.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (d_FB cx + 1664 <= a < d_FB cx + 1668) ->
  aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem3 a).
{ apply (jt_kept_frame _ _ (w_H W) mem3 memc (d_FB cx + 1664) (d_FB cx + 1668) HFr).
  intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val];
     first [left; lia | right; rewrite d_env_old by (cbv; lia); change 516%nat with AT_F; rewrite HFU; lia] | ]).
  destruct Hr. }
assert (KV : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat nb -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668)) ->
  val_mem SEGS (rd W mem3) a nb v -> val_mem SEGS (rd W memc) a nb v).
{ intros a nb v Ha Hb Hx Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memc); [|exact Hv].
  intros kk Hkk. apply KC; [lia | apply Hx; lia]. }
assert (KG : forall a L, 0 <= a -> a + Z.of_nat (length L) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length L) -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668)) ->
  garr8 SEGS (rd W mem3) a L -> garr8 SEGS (rd W memc) a L).
{ intros a L Ha Hb Hx Hv. eapply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 memc); [|exact Hv].
  intros x Hx'. apply KC; [lia | apply Hx; lia]. }
assert (H216c : val_mem SEGS (rd W memc) (d_A cx + 216) 8 h) by (apply KV; [lia | lia | intros x Hx; lia | exact H216]).
assert (H152c : val_mem SEGS (rd W memc) (d_A cx + 152) 8 (h + 440))
  by (apply KV; [lia | lia | intros x Hx; lia | exact H152]).
assert (HCTXc : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W memc mdc k) by exact (conj HBASE (conj HJ HFRS)).
pose proof (DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W mdc k (d_env cx E (a3f_vals regs)) _ ms HCTXc
  (d_E_env cx E (a3f_vals regs) HdE) (d_env_fl cx E (a3f_vals regs)) HSpi ltac:(vm_compute; reflexivity)
  H216c H152c) as (HFRMc & HSHDc).
assert (HBODYc : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W memc).
{ apply (d_body_rt B cx h n n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W mem3 memc (d_A cx) (d_A cx)
    (fun a => d_FB cx + 1664 <= a < d_FB cx + 1668) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right. unfold d_rdset, d_objr. pose proof HGEO as (_ & _ & _ & _ & _ & _ & Gh & Gp).
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Gh, Gp. unfold slot_inv.HUNT_SIZE in Gh.
    intros [Hx | [Hx | [Hx | [Hx | [Hx | [Hx | [(Hro & _ & _) | Hcn]]]]]]].
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold slot_inv.HUNT_SIZE in Hx. lia.
    + destruct Hx as (Hc & Hx). specialize (Gp Hc). lia.
    + exact (off_img_not_img (d_FB cx) 4096 a GFoff ltac:(lia) (in_roP_img a Hro)).
    + exact (off_img_not_img (d_FB cx) 4096 a GFoff ltac:(lia) (proj2 (proj2 HCAN) a Hcn)).
  - intros a Ha Hna. exact (KC a Ha Hna).
  - intros a _ Hp. eapply apresent_grows; [exact HG | exact Hp].
  - exact HFRMc.
  - exact HSHDc.
  - lia. }
pose proof HBODYc as (Tc & Gc & Lkc & Hc & _ & _ & _ & _ & _ & HIMGc & _).
pose proof (proj1 HJ) as HARc.
pose proof (DCRO LAWS (conj DRO (conj GM (HV))) ly3 S3 W memc mdc HARc HIMGc) as (_ & _ & _ & HSTRS & _).
pose proof (a3f_rolestr W memc 1 ltac:(lia) HSTRS) as HKEY.
change (a3f_roleobj 1) with 13%nat in HKEY.
set (txt := disco_json_text.rolename 1) in *.
destruct HKEY as ((KF & KG0 & Kx0 & Kx63 & Kx32 & KAM & KRA & KSH & KTL & KIMG) & KROM).
set (xk := VAL (A_OBJ 13)) in *.
destruct (pfxa_slack (w_H W) memc xk (txt ++ [0]) (Z.to_nat ((- (xk + Z.of_nat (length txt) + 1)) mod 8)) KG0)
  as (sl & Hsl & KG1).
{ intros j Hj. rewrite length_app. cbn [length]. apply KTL. lia. }
assert (KG2 : garr8 SEGS (rd W memc) xk
  (map (fun b : byte => bv_unsigned b) (printf_facts_c.pf_bytes txt ++ Z_to_bv 8 0 :: sl))).
{ rewrite map_app. cbn [map]. rewrite pfxa_pfb by (eapply Forall_impl; [|exact KF]; intros cc Hcc; cbv beta in Hcc; lia).
  change (bv_unsigned (Z_to_bv 8 0)) with 0. rewrite <- app_assoc in KG1. exact KG1. }
assert (HTL : length (printf_facts_c.pf_bytes txt) = length txt) by (unfold printf_facts_c.pf_bytes; apply length_map).
set (X := a3_text T1 now) in *.
assert (LXeq : Z.of_nat (length (a3_text T1 now)) = Z.of_nat (length X)) by reflexivity.
set (t := nth 1 (nth 0 os []) disco_json_reader_model.tok_none).
pose proof (a3f_obj T1 now count os 0 LT1 TOK1 Hnow HJR ltac:(lia)) as HOB0. cbv zeta in HOB0.
destruct HOB0 as (_ & HRT & _).
change (Z.to_nat 0) with 0%nat in HRT.
change (disco_json_text.e_role (reac_disco_table_json_c.tj_entry T1 0)) with (disco_table_c.role_of_e T1 0) in HRT.
rewrite Er in HRT. fold X t txt in HRT.
pose proof HRT as HRT'. unfold disco_json_reader_model.jtok_is in HRT'.
apply andb_prop in HRT' as [HRT1 HRT3]. apply andb_prop in HRT1 as [HRk HRn].
apply Z.eqb_eq in HRk, HRn. apply disco_json_lemmas.lzeqb_true in HRT3.
assert (Hlos : (0 < length os)%nat) by lia.
assert (Ho6 : length (nth 0 os []) = 6%nat) by (apply (proj1 (Forall_forall _ _) H6); apply nth_In; lia).
assert (Htin : In t (nth 0 os [])) by (unfold t; apply nth_In; rewrite Ho6; lia).
pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Hinb (nth 0 os []) (nth_In _ _ Hlos)) t Htin) as Htb.
unfold slot_ser_tokb.tok_inb, disco_jscalar_model.jlen in Htb.
destruct Htb as [Hk0 | (Hs0 & Hl0 & Hsl0)]; [fold t in Hk0; lia|].
fold t in Hs0, Hl0, Hsl0.
pose proof HBUF as (HBr & HBG). unfold a3_r in HBr. fold X in HBr, HBG.
assert (HinB : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ pose proof HBLK as (HPerm0 & _). apply (Permutation_in _ (Permutation_sym HPerm0)).
  apply in_or_app. left. left. reflexivity. }
assert (Hrq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W memc mdc buf _ DFRAME_CLASS (c_fpos cx) HARc HinB HFin3) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. rewrite EFA3, Hrq in HdBF.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HdBF.
assert (HTXL : Z.of_nat (length txt) = snd t) by lia.
destruct (pfxa_heap ly3 S3 W memc mdc buf _ (buf + snd (fst t)) (Z.of_nat (length txt)) HARc HinB ltac:(lia)
  ltac:(rewrite Hrq; lia) ltac:(lia)) as (PAM & PRA & PSH & Pb4096 & Pbceil).
rewrite Hrq in Pbceil.
assert (HBGc : garr8 SEGS (rd W memc) buf (X ++ [0])).
{ apply KG; [lia | rewrite length_app; cbn [length]; lia | intros x Hx; rewrite length_app in Hx; cbn [length] in Hx; lia | exact HBG]. }
assert (HPG : garr8 SEGS (rd W memc) (buf + snd (fst t))
  (map (fun b : byte => bv_unsigned b) (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)))).
{ rewrite pfxa_pfb.
  2: { rewrite HRT3. eapply Forall_impl; [|exact KF]; intros cc Hcc; cbv beta in Hcc; lia. }
  pose proof (garr8_sub_x SEGS _ _ _ (Z.to_nat (snd (fst t))) (Z.to_nat (snd t)) HBGc
    ltac:(rewrite length_app; cbn [length]; lia)) as Gsub.
  rewrite Z2Nat.id in Gsub by lia.
  unfold disco_json_reader_model.tv_text.
  rewrite skipn_app, firstn_app in Gsub.
  replace (Z.to_nat (snd t) - length (skipn (Z.to_nat (snd (fst t))) X))%nat with 0%nat in Gsub
    by (rewrite length_skipn; lia).
  cbn [firstn] in Gsub. rewrite app_nil_r in Gsub. exact Gsub. }
assert (HOOc : garr8 SEGS (rd W memc) (d_obj cx OO)
  (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))).
{ assert (LOSn : (length (slot_ser_defs.objs_bytes buf vpad os) = 144 * Z.to_nat count)%nat)
    by (rewrite (slot_ser_Pq.objs_len buf vpad os HVP H6); f_equal; exact Los).
  assert (LOO : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)))
    = 144 * count) by (rewrite length_map, LOSn; lia).
  apply KG; [unfold d_obj, dobj_off; lia | rewrite LOO; unfold d_obj, dobj_off; lia |
    intros x Hx; rewrite LOO in Hx; unfold d_obj, dobj_off in Hx; lia | exact HOO]. }
pose proof (pfxa_slot01 _ _ buf vpad os HVP H6 Hlos HOOc) as HSL. fold t in HSL.
destruct (pfxa_slot_vals _ _ buf vpad t HVP ltac:(lia) HSL ltac:(lia) ltac:(lia) ltac:(lia)) as (Mvp & Mvn & Mvk).
unfold d_obj, dobj_off in Mvp, Mvn, Mvk.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat
  (YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 1664 1668
     (YP09.mkChunk 1664 (CVal 4 (SLit 1)) :: dfhdr_chunks ++ [YP09.mkChunk 2168 (CVal 4 (SLit 1))]))
  HSpi eq_refl) as HR516.
assert (HG1664 : garr8 SEGS (rd W memc) (d_obj cx OUSED) [1; 0; 0; 0]).
{ pose proof (Forall_inv (proj2 (proj2 (proj2 HR516)))) as HC1.
  cbn [YP09.r_base base_val] in HC1. rewrite d_env_old in HC1 by (cbv; lia).
  change 516%nat with AT_F in HC1. rewrite HFU in HC1.
  pose proof (ReacHuntPin.pin_garr8_le4 SEGS (d_env cx E (a3f_vals regs)) (rd W memc) (d_FB cx) 1664
    (SLit 1) (Z_to_bv 64 1) HC1 eq_refl) as HG0.
  replace (map (fun b : byte => bv_unsigned b) (Mem.le4 (Z_to_bv 64 1))) with [1; 0; 0; 0] in HG0
    by (vm_compute; reflexivity).
  unfold d_obj, dobj_off. exact HG0. }
assert (HMCin : In (McConsts.MC_CONSTS_LO, 32) disco_ro_ranges).
{ unfold disco_ro_ranges. apply in_or_app. right. cbn. repeat (first [left; reflexivity | right]). }
replace (d_FB cx + 240 + 24) with (d_FB cx + 264) in Mvp, Mvn, Mvk by lia.
assert (HMCro : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a).
{ intros a Ha. apply (disco_ro_in_ro _ _ a (in_or_app _ _ _ (or_introl HMCin))).
  unfold McConsts.MC_CONSTS_LO, McConsts.MC_CONSTS_HI in Ha |- *. lia. }
assert (HMCun : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. apply (disco_ro_unowned_at B _ _ DRO HMCin a).
  unfold McConsts.MC_CONSTS_LO, McConsts.MC_CONSTS_HI in Ha |- *. lia. }
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W memc mdc k HCTXc)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpresc & GSHc & GSTKc & _ & _ & _ & _).
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
pose proof (pa_img_range xk (KIMG xk ltac:(lia))) as XR. unfold IMG_LO, IMG_TOP in XR.
assert (Ltxt : (length txt <= 7)%nat) by (unfold txt; cbv; lia).
assert (Lsl : (length sl <= 7)%nat) by (rewrite Hsl; pose proof (Z.mod_pos_bound (- (xk + Z.of_nat (length txt) + 1)) 8 ltac:(lia)); lia).
eapply SRr_bind; [apply (aj_jtok_at B LAWS TJTOK fq W R memc LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 mdc k (d_A cx - d_S cx) (d_FB cx + 264) xk 1 1
    (buf + snd (fst t)) (snd t) (printf_facts_c.pf_bytes txt) sl
    (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)) HJ) |].
- rewrite SpR. lia.
- lia.
- lia.
- rewrite Htk. unfold LLVMF_STK. lia.
- rewrite Q3. exact Rgp.
- rewrite Q4. exact Rtp.
- rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
- unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
- exact HIMGc.
- exact (mc_cv_ok B W memc HMCro HMCun HIMGc).
- exact Q10.
- exact Q11.
- exact Q12.
- lia.
- lia.
- lia.
- lia.
- lia.
- exact Mvp.
- exact Mvn.
- change (1 mod 2 ^ 32) with 1. rewrite <- HRk. exact Mvk.
- lia.
- lia.
- apply (amem_range_sub_app (d_FB cx) 4096); [exact GFapp | lia | lia | lia | lia].
- exact (pfxa_tok_ra cx W memc HSHDc ltac:(lia) ltac:(lia)).
- exact (pfxa_tok_hull cx W memc GSHc GF32 ltac:(lia)).
- left. rewrite SpR, Htk. lia.
- exact (slot_ser_Pq.pf_no_zero txt KF).
- exact KG2.
- rewrite HTL, Hsl. rewrite Z2Nat.id; [lia | apply Z.mod_pos_bound; lia].
- exact Kx0.
- rewrite HTL. lia.
- rewrite HTL. lia.
- rewrite HTL. replace (Z.of_nat (length txt + 1)) with (Z.of_nat (length txt) + 1) by lia. exact KAM.
- rewrite HTL. replace (Z.of_nat (length txt + 1)) with (Z.of_nat (length txt) + 1) by lia. exact KRA.
- rewrite HTL. replace (Z.of_nat (length txt + 1)) with (Z.of_nat (length txt) + 1) by lia. exact KSH.
- left. rewrite SpR, Htk, HTL. lia.
- intros _ _.
  assert (LP : length (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)) =
    length (printf_facts_c.pf_bytes txt)) by (rewrite HRT3; reflexivity).
  rewrite LP, HTL.
  split; [reflexivity|]. split; [exact HPG|]. split; [lia|]. split; [lia|].
  split; [exact PAM|]. split; [exact PRA|]. split; [exact PSH|].
  left. rewrite SpR, Htk. lia.
- intros W2 c2 HW2 (fq2 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hcsr2 & HJ4 & HJc & HP4 & HPerm & HKeep & Hres).
  assert (HXb : Forall (fun cc => 0 <= cc < 256) X) by (eapply Forall_impl; [|exact Hg33]; intros cc Hcc; cbv beta in Hcc; lia).
  pose proof (proj2 (slot_ser_Pq.jt_iff X t 1 txt HXb KF ltac:(lia)) HRT) as HM. rewrite HRk in HM.
  assert (R10 : getr regs4 10 = w64 1) by (destruct Hres as [(_ & H10) | (Hn10 & _)]; [exact H10 | contradiction]).
  rewrite SpR, Htk in HKeep.
  pose proof HJc as (_ & _ & _ & _ & _ & HfrC & _).
  assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFRS).
  assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR4)).
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 k HCTX4)
    as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
  destruct HFRMc as (E2 & HdE2 & HREG2 & HFLAG2 & _ & _).
  pose proof HdE2 as (HER2 & HE322 & HEI2 & HEA2 & HEF2 & HESH2).
  assert (HEId2 : img_env VAL A_LIM (d_env cx E2 (map (getr R) (tl all_regs))))
    by (apply img_env_havoc_hi; [exact HEI2 | unfold AT_FL, A_LIM; lia]).
  pose proof (DSEAT LAWS PAL fq2 cx dsh_ser2 ly3 S3 W R memc mdc k E2 AF_jtok_is
    (SLit 0 :: SOff A_TEXT 8104 :: atom_regs 532 30) (map (getr R) (tl all_regs)) [] [] [] (d_facts [] [])
    HCTXc HdE2 HREG2 HFLAG2 (pfxa_regs2 cx E2 R HEI2 Q1)
    (DFACTS LAWS cx ly3 S3 W memc mdc k E2 (map (getr R) (tl all_regs)) [] [] HCTXc HdE2 I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HSC.
  jafter_call_keep_hi HSC 562%nat regs4 (mrestrict (w_H W2) mem4) HP4 [0;1;2;3]%nat HS2.
  match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
  { cbn [ms_mem restrict YK11.mkst]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (d_S cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). rewrite (HER2 2%nat 2%bv eq_refl). reflexivity.
      + intros a Ha. apply HKeep; lia.
      + intros a Ha. lia.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (d_A cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite HEA2. unfold w64.
        apply unsigned_lit_small. lia.
      + intros a Ha. apply HKeep; lia.
      + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (d_FB cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite HEF2. unfold w64.
        apply unsigned_lit_small. lia.
      + intros a Ha. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. apply HKeep; lia.
      + intros a Ha. apply GFpres4. unfold DFRAME_SIZE in Ha. lia.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (shadow_addr (d_FB cx))).
      + rewrite d_env_old by (unfold AT_FL; lia). change 529%nat with AT_SH. rewrite HESH2. unfold w64.
        apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia.
      + intros a Ha. apply HKeep; unfold shadow_addr, SHADOW_OFF in *; lia.
      + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
        apply GFsh4. lia. }
  specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
  assert (HE3 : d_E cx (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
    by (apply pfxa_dE; [apply d_E_env; exact HdE2 | lia]).
  assert (HFL3 : ew (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
    Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
    by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
  assert (HEI3 : img_env VAL A_LIM (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
    by (apply img_env_havoc_hi; [exact HEId2 | unfold A_LIM; lia]).
  pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 1 HS2 ltac:(cbn [ms_regs restrict YK11.mkst]; exact R10) eq_refl)
    as HS3.
  clear HS2.
  pose proof (st_ok_pi_submem _ _ _ _ HS3 (pfxa_narrow0_sub _) ltac:(vm_compute; reflexivity)) as HS4.
  clear HS3. cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS4. norm_ss HS4.
  rewrite Q1.
  pose proof HJ4 as HJ4c.
  clear HF HFr HG.
  pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq2) B LAWS).
  paj_run_to_shc RUNTOP HS4 HJ4 R1_OFF.
  + lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil.
  + assert (Emem : ms_mem ms0 = mem4).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hr & Hw).
      vm_compute in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia|]). destruct Hr. }
    pmkst HS4.
    prreg HS4 (2%bv : bv 5) F2. prreg HS4 (3%bv : bv 5) F3. prreg HS4 (4%bv : bv 5) F4. prreg HS4 (8%bv : bv 5) F8.
    prreg HS4 (9%bv : bv 5) F9. prreg HS4 (18%bv : bv 5) F18. prreg HS4 (20%bv : bv 5) F20.
    prreg HS4 (24%bv : bv 5) F24. prreg HS4 (25%bv : bv 5) F25. prreg HS4 (26%bv : bv 5) F26.
    assert (KV4 : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat nb -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668) /\ ~ (d_A cx - 8240 <= x < d_A cx)) ->
      val_mem SEGS (rd W mem3) a nb v -> val_mem SEGS (rd W2 mem4) a nb v).
    { intros a nb v Ha Hb Hx Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
      intros kk Hkk. destruct (Hx (a + kk) ltac:(lia)) as (Hx1 & Hx2).
      rewrite (HKeep (a + kk) ltac:(lia) Hx2). apply KC; [lia | exact Hx1]. }
    assert (KG4 : forall a L, 0 <= a -> a + Z.of_nat (length L) <= 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat (length L) -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668) /\ ~ (d_A cx - 8240 <= x < d_A cx)) ->
      garr8 SEGS (rd W mem3) a L -> garr8 SEGS (rd W2 mem4) a L).
    { intros a L Ha Hb Hx Hv. eapply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
      intros x Hx'. destruct (Hx x Hx') as (Hx1 & Hx2).
      rewrite (HKeep x ltac:(lia) Hx2). apply KC; [lia | exact Hx1]. }
    assert (H216f : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 216) 8 h)
      by (rewrite Emem; apply KV4; [lia | lia | intros x Hx; split; lia | exact H216]).
    assert (H152f : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 152) 8 (h + 440))
      by (rewrite Emem; apply KV4; [lia | lia | intros x Hx; split; lia | exact H152]).
    assert (HCTXf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 (ms_mem ms0)
      (with_vm_backing (m_vm_lazy md4) mat0 md4) k) by exact (conj HBASE (conj HJ4 HFR4)).
    pose proof (DLAND LAWS FFL fq2 cx h dsh_ser2 ly4 S4 W2 (with_vm_backing (m_vm_lazy md4) mat0 md4) k
      (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) _ ms0 HCTXf HE3 HFL3 HS4
      ltac:(vm_compute; reflexivity) H216f H152f) as (HFRMf & HSHDf).
    rewrite Emem in HFRMf, HSHDf, HJ4.
    pose proof (d_body_call_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W memc
      ly4 S4 W2 mem4 md4 k (d_A cx - 8240) (d_A cx) HBODYc (conj HBASE HJ4c) ltac:(unfold LLVMF_STK; lia) ltac:(lia)
      ltac:(intros a Ha Hna; exact (HKeep a Ha Hna)) HPerm HFRMf HSHDf) as HBODYf.
    assert (F2' : getr (ms_regs ms0) 2 = getr R 2)
      by (rewrite F2; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 1 ltac:(rewrite length_map; cbn; lia))).
    assert (F3' : getr (ms_regs ms0) 3 = getr R 3)
      by (rewrite F3; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 2 ltac:(rewrite length_map; cbn; lia))).
    assert (F4' : getr (ms_regs ms0) 4 = getr R 4)
      by (rewrite F4; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 3 ltac:(rewrite length_map; cbn; lia))).
    assert (F8' : getr (ms_regs ms0) 8 = getr R 8)
      by (rewrite F8; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 7 ltac:(rewrite length_map; cbn; lia))).
    assert (F9' : getr (ms_regs ms0) 9 = getr R 9)
      by (rewrite F9; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 8 ltac:(rewrite length_map; cbn; lia))).
    assert (F18' : getr (ms_regs ms0) 18 = getr R 18)
      by (rewrite F18; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 17 ltac:(rewrite length_map; cbn; lia))).
    assert (F20' : getr (ms_regs ms0) 20 = getr R 20)
      by (rewrite F20; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 19 ltac:(rewrite length_map; cbn; lia))).
    assert (F24' : getr (ms_regs ms0) 24 = getr R 24)
      by (rewrite F24; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 23 ltac:(rewrite length_map; cbn; lia))).
    assert (F25' : getr (ms_regs ms0) 25 = getr R 25)
      by (rewrite F25; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 24 ltac:(rewrite length_map; cbn; lia))).
    assert (F26' : getr (ms_regs ms0) 26 = getr R 26)
      by (rewrite F26; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 25 ltac:(rewrite length_map; cbn; lia))).
    assert (HU1 : garr8 SEGS (rd W2 mem4) (d_obj cx OUSED) (a3f_used 1)).
    { assert (EU1 : a3f_used 1 = [1; 0; 0; 0] ++ skipn 4 (a3f_used 0)) by (vm_compute; reflexivity).
      rewrite EU1. apply garr8_app. split.
      - apply (garr8_aview_kept SEGS (w_H W) (w_H W2) memc mem4 (d_obj cx OUSED) [1;0;0;0]); [|exact HG1664].
        intros x Hx. cbn [length] in Hx. apply HKeep; unfold d_obj, dobj_off in *; lia.
      - cbn [length].
        assert (HT0 : garr8 SEGS (rd W mem3) (d_obj cx OUSED + 4) (skipn 4 (a3f_used 0))).
        { rewrite <- (firstn_skipn 4 (a3f_used 0)) in HUSED.
          apply garr8_app in HUSED as [_ HUt].
          replace (length (firstn 4 (a3f_used 0))) with 4%nat in HUt by (vm_compute; reflexivity).
          exact HUt. }
        apply KG4; [unfold d_obj, dobj_off; lia | | | exact HT0];
          replace (length (skipn 4 (a3f_used 0))) with 28%nat by (vm_compute; reflexivity);
          [|intros x Hx; split]; unfold d_obj, dobj_off in *; lia. }

    rewrite Emem.
    apply SRr_ret.
    unfold f_r1, a3f_st. split.
    { destruct HFROM as (HA3 & HW0 & HL0 & HEX). split; [exact HA3|].
      split; [eapply wle_trans; [exact HW0 | exact HW2]|]. split; [exact HL0 | exact HEX]. }
    unfold d_arm_at_pf, d_at.
    exists fq2, ly4, S4, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), k, acc.
    split; [unfold cfg_at, w64, R1_OFF; reflexivity|].
    split; [destruct Hcsr2 as [Hcs | Hcs]; [rewrite Hcs; assumption | exact Hcs]|]. split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|]. split; [exact Hk|].
    split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
    split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
    split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
    pose proof HSP1 as ((H232 & H344) & H224 & H248).
    split.
    { split; [unfold spZ; rewrite F2'; exact SpR|].
      split; [rewrite F3', Q3; exact Rgp|]. split; [rewrite F4', Q4; exact Rtp|].
      split; [rewrite F8', Q8; unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
      split; [rewrite F9'; exact Q9|]. split; [rewrite F18'; exact Q18|].
      split; [rewrite F20'; exact Q20|]. rewrite F25'; exact Q25. }
    split.
    { split; [rewrite F26', Q26; exact R26|]. rewrite F24', Q24. unfold w64, d_obj, dobj_off. f_equal. lia. }
    split.
    { split.
      { split; [split|split].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H232].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H344].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H224].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H248]. }
      split.
      { split; [exact (proj1 HTAB)|].
        apply KG4; [unfold d_obj, dobj_off; lia | | | exact HOT];
          rewrite length_map, LT1; [|intros x Hx; split]; unfold d_obj, dobj_off in *; lia. }
      split.
      { split; [exact HBr|].
        apply KG4; [lia | | | exact HBG]; rewrite length_app; cbn [length];
          [|intros x Hx; split]; lia. }
      split; [exact HJR|]. split; [exact HVP|].
      split.
      { assert (LOSn : (length (slot_ser_defs.objs_bytes buf vpad os) = 144 * Z.to_nat count)%nat)
          by (rewrite (slot_ser_Pq.objs_len buf vpad os HVP H6); f_equal; exact Los).
        assert (LOO : Z.of_nat (length (map (fun b : byte => bv_unsigned b)
          (slot_ser_defs.objs_bytes buf vpad os))) = 144 * count) by (rewrite length_map, LOSn; lia).
        apply KG4; [unfold d_obj, dobj_off; lia | rewrite LOO; unfold d_obj, dobj_off; lia |
          intros x Hx; rewrite LOO in Hx; unfold d_obj, dobj_off in Hx; split; lia | exact HOO]. }
      split.
      { split; [exact Hpc|].
        split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H368]|].
        apply KV4; [lia | lia | intros x Hx; split; lia | exact H336]. }
      split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H392]|].
      split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H408]|].
      exact HU1. }
    split.
    { split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H232]|].
      apply KV4; [lia | lia | intros x Hx; split; lia | exact H344]. }
    exact HBODYf.
}
{
pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PFX_OFF (a3f_sr 0) (a3f_vals regs)
  pfxa_acs (pfxa_fcs 2) [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (a3f_regs_ok cx E 0 regs HdE HA64 ltac:(rewrite Z.add_0_r; exact Rsp) R8 R9 R18 R20 R25)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (a3f_vals regs) [] [] HCTX HdE I I)) as HSEED.
match type of HSEED with ?Q -> _ => assert (HACS : Q) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (chunk_ok_val _ _ _ _ _ _ _ (d_obj cx OO + 144 * 0)).
    + cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
      unfold d_obj, dobj_off. f_equal. lia.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold d_obj, dobj_off. lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H392.
  - eapply (chunk_ok_val _ _ _ _ _ _ _ 0).
    + reflexivity.
    + lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H408. }
specialize (HSEED HACS). clear HACS.
match type of HSEED with ?Q -> _ => assert (HFCS : Q) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. exact V1664.
  - eapply (chunk_ok_val _ _ _ _ _ _ _ 2); [reflexivity | lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. exact V2168. }
specialize (HSEED HFCS). clear HFCS.
pose proof (HSEED (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
clear HSEED. unfold ss_d in HS0. rewrite app_nil_r in HS0.
pose proof (st_ok_pi_submem _ _ _ _ HS0 (pfxa_narrow_sub dsh_ser2 pfxa_acs (pfxa_fcs 2)) ltac:(vm_compute; reflexivity))
  as HS1.
clear HS0. cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS1.
pose proof (ast_ok_pi_set_reg_fp _ _ _ (14%bv : bv 5) (SOff AT_F 2160) HS1 eq_refl) as HS2.
clear HS1.
assert (HS : st_ok_pi (fx := fq) SEGS VAL (d_env cx E (a3f_vals regs))
  (mkSS PFX_OFF (sr_set (a3f_sr 0) (14%bv : bv 5) (SOff AT_F 2160))
     (pfxa_narrow (d_kregions dsh_ser2 pfxa_acs (pfxa_fcs 2))) None (d_facts [] []))
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PFX_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ apply HS2. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  rewrite restrict_mkst_fx. cbn [ms_regs YK11.mkst]. unfold d_obj, dobj_off in R14. rewrite R14. reflexivity. }
clear HS2.
norm_ss HS.
rewrite Ec. unfold cfg_at. change (w64 (BASE + PFX_OFF)) with (Z_to_bv 64 (BASE + PFX_OFF)).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (a3f_vals regs)) (rd W (ms_mem (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PFX_OFF)) mem3 (YK11.seg_rom SEGS))))) by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN HS HJ SHOK (0, 0).
1: { lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
       let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end.
     apply awr_ok_cons_ro; [cbn; lia|].
     apply awr_ok_cons_ro; [cbn; lia|].
     eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat (d_FB cx)).
     - reflexivity.
     - rewrite d_env_old by (cbv; lia). exact HFU.
     - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply (HAWRF a). unfold DFRAME_SIZE. lia.
     - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS.
rewrite pa_sigma_jtok_is. rewrite pa_sigma_jtok_is in HS.
pose proof (pfxa_st_ok_pi fq _ _ _ AF_jtok_is HS) as HSpi.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
clear HS.
set (R := ms_regs ms) in *.
set (memc := ms_mem ms) in *.
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
rewrite (a3f_env_reg cx E regs 3%bv 534 eq_refl) in Q3.
rewrite (a3f_env_reg cx E regs 4%bv 535 eq_refl) in Q4.
rewrite (a3f_env_reg cx E regs 26%bv 557 eq_refl) in Q26.
rewrite (d_env_old cx E (a3f_vals regs) 60) in Q2, Q9 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 2) in Q8 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 32) in Q18 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 516) in Q10, Q24 by (cbv; lia).
rewrite (d_env_old cx E (a3f_vals regs) 253) in Q12 by (cbv; lia).
change (ew E 516) with (ew E AT_F) in Q10, Q24. rewrite HFU in Q10, Q24.
change (ew E 60) with (ew E AT_A) in Q2, Q9. rewrite HEA in Q2, Q9.
rewrite HE32 in Q18.
rewrite (HER 2%nat 2%bv eq_refl) in Q8.
rewrite (img_env_atomP E 253 HEI0 ltac:(cbv; lia)) in Q12.
assert (SpR : spZ R = d_A cx) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (Htk : TJTOK_IS_STK = 8240) by reflexivity.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (d_FB cx + 1664 <= a < d_FB cx + 1668) ->
  aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem3 a).
{ apply (jt_kept_frame _ _ (w_H W) mem3 memc (d_FB cx + 1664) (d_FB cx + 1668) HFr).
  intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val];
     first [left; lia | right; rewrite d_env_old by (cbv; lia); change 516%nat with AT_F; rewrite HFU; lia] | ]).
  destruct Hr. }
assert (KV : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat nb -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668)) ->
  val_mem SEGS (rd W mem3) a nb v -> val_mem SEGS (rd W memc) a nb v).
{ intros a nb v Ha Hb Hx Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 memc); [|exact Hv].
  intros kk Hkk. apply KC; [lia | apply Hx; lia]. }
assert (KG : forall a L, 0 <= a -> a + Z.of_nat (length L) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length L) -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668)) ->
  garr8 SEGS (rd W mem3) a L -> garr8 SEGS (rd W memc) a L).
{ intros a L Ha Hb Hx Hv. eapply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 memc); [|exact Hv].
  intros x Hx'. apply KC; [lia | apply Hx; lia]. }
assert (H216c : val_mem SEGS (rd W memc) (d_A cx + 216) 8 h) by (apply KV; [lia | lia | intros x Hx; lia | exact H216]).
assert (H152c : val_mem SEGS (rd W memc) (d_A cx + 152) 8 (h + 440))
  by (apply KV; [lia | lia | intros x Hx; lia | exact H152]).
assert (HCTXc : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W memc mdc k) by exact (conj HBASE (conj HJ HFRS)).
pose proof (DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W mdc k (d_env cx E (a3f_vals regs)) _ ms HCTXc
  (d_E_env cx E (a3f_vals regs) HdE) (d_env_fl cx E (a3f_vals regs)) HSpi ltac:(vm_compute; reflexivity)
  H216c H152c) as (HFRMc & HSHDc).
assert (HBODYc : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W memc).
{ apply (d_body_rt B cx h n n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W mem3 memc (d_A cx) (d_A cx)
    (fun a => d_FB cx + 1664 <= a < d_FB cx + 1668) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right. unfold d_rdset, d_objr. pose proof HGEO as (_ & _ & _ & _ & _ & _ & Gh & Gp).
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Gh, Gp. unfold slot_inv.HUNT_SIZE in Gh.
    intros [Hx | [Hx | [Hx | [Hx | [Hx | [Hx | [(Hro & _ & _) | Hcn]]]]]]].
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold d_obj, dobj_off, dobj_size in Hx. lia.
    + unfold slot_inv.HUNT_SIZE in Hx. lia.
    + destruct Hx as (Hc & Hx). specialize (Gp Hc). lia.
    + exact (off_img_not_img (d_FB cx) 4096 a GFoff ltac:(lia) (in_roP_img a Hro)).
    + exact (off_img_not_img (d_FB cx) 4096 a GFoff ltac:(lia) (proj2 (proj2 HCAN) a Hcn)).
  - intros a Ha Hna. exact (KC a Ha Hna).
  - intros a _ Hp. eapply apresent_grows; [exact HG | exact Hp].
  - exact HFRMc.
  - exact HSHDc.
  - lia. }
pose proof HBODYc as (Tc & Gc & Lkc & Hc & _ & _ & _ & _ & _ & HIMGc & _).
pose proof (proj1 HJ) as HARc.
pose proof (DCRO LAWS (conj DRO (conj GM (HV))) ly3 S3 W memc mdc HARc HIMGc) as (_ & _ & _ & HSTRS & _).
pose proof (a3f_rolestr W memc 2 ltac:(lia) HSTRS) as HKEY.
change (a3f_roleobj 2) with 12%nat in HKEY.
set (txt := disco_json_text.rolename 2) in *.
destruct HKEY as ((KF & KG0 & Kx0 & Kx63 & Kx32 & KAM & KRA & KSH & KTL & KIMG) & KROM).
set (xk := VAL (A_OBJ 12)) in *.
destruct (pfxa_slack (w_H W) memc xk (txt ++ [0]) (Z.to_nat ((- (xk + Z.of_nat (length txt) + 1)) mod 8)) KG0)
  as (sl & Hsl & KG1).
{ intros j Hj. rewrite length_app. cbn [length]. apply KTL. lia. }
assert (KG2 : garr8 SEGS (rd W memc) xk
  (map (fun b : byte => bv_unsigned b) (printf_facts_c.pf_bytes txt ++ Z_to_bv 8 0 :: sl))).
{ rewrite map_app. cbn [map]. rewrite pfxa_pfb by (eapply Forall_impl; [|exact KF]; intros cc Hcc; cbv beta in Hcc; lia).
  change (bv_unsigned (Z_to_bv 8 0)) with 0. rewrite <- app_assoc in KG1. exact KG1. }
assert (HTL : length (printf_facts_c.pf_bytes txt) = length txt) by (unfold printf_facts_c.pf_bytes; apply length_map).
set (X := a3_text T1 now) in *.
assert (LXeq : Z.of_nat (length (a3_text T1 now)) = Z.of_nat (length X)) by reflexivity.
set (t := nth 1 (nth 0 os []) disco_json_reader_model.tok_none).
pose proof (a3f_obj T1 now count os 0 LT1 TOK1 Hnow HJR ltac:(lia)) as HOB0. cbv zeta in HOB0.
destruct HOB0 as (_ & HRT & _).
change (Z.to_nat 0) with 0%nat in HRT.
change (disco_json_text.e_role (reac_disco_table_json_c.tj_entry T1 0)) with (disco_table_c.role_of_e T1 0) in HRT.
rewrite Er in HRT. fold X t txt in HRT.
pose proof HRT as HRT'. unfold disco_json_reader_model.jtok_is in HRT'.
apply andb_prop in HRT' as [HRT1 HRT3]. apply andb_prop in HRT1 as [HRk HRn].
apply Z.eqb_eq in HRk, HRn. apply disco_json_lemmas.lzeqb_true in HRT3.
assert (Hlos : (0 < length os)%nat) by lia.
assert (Ho6 : length (nth 0 os []) = 6%nat) by (apply (proj1 (Forall_forall _ _) H6); apply nth_In; lia).
assert (Htin : In t (nth 0 os [])) by (unfold t; apply nth_In; rewrite Ho6; lia).
pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Hinb (nth 0 os []) (nth_In _ _ Hlos)) t Htin) as Htb.
unfold slot_ser_tokb.tok_inb, disco_jscalar_model.jlen in Htb.
destruct Htb as [Hk0 | (Hs0 & Hl0 & Hsl0)]; [fold t in Hk0; lia|].
fold t in Hs0, Hl0, Hsl0.
pose proof HBUF as (HBr & HBG). unfold a3_r in HBr. fold X in HBr, HBG.
assert (HinB : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ pose proof HBLK as (HPerm0 & _). apply (Permutation_in _ (Permutation_sym HPerm0)).
  apply in_or_app. left. left. reflexivity. }
assert (Hrq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W memc mdc buf _ DFRAME_CLASS (c_fpos cx) HARc HinB HFin3) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. rewrite EFA3, Hrq in HdBF.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HdBF.
assert (HTXL : Z.of_nat (length txt) = snd t) by lia.
destruct (pfxa_heap ly3 S3 W memc mdc buf _ (buf + snd (fst t)) (Z.of_nat (length txt)) HARc HinB ltac:(lia)
  ltac:(rewrite Hrq; lia) ltac:(lia)) as (PAM & PRA & PSH & Pb4096 & Pbceil).
rewrite Hrq in Pbceil.
assert (HBGc : garr8 SEGS (rd W memc) buf (X ++ [0])).
{ apply KG; [lia | rewrite length_app; cbn [length]; lia | intros x Hx; rewrite length_app in Hx; cbn [length] in Hx; lia | exact HBG]. }
assert (HPG : garr8 SEGS (rd W memc) (buf + snd (fst t))
  (map (fun b : byte => bv_unsigned b) (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)))).
{ rewrite pfxa_pfb.
  2: { rewrite HRT3. eapply Forall_impl; [|exact KF]; intros cc Hcc; cbv beta in Hcc; lia. }
  pose proof (garr8_sub_x SEGS _ _ _ (Z.to_nat (snd (fst t))) (Z.to_nat (snd t)) HBGc
    ltac:(rewrite length_app; cbn [length]; lia)) as Gsub.
  rewrite Z2Nat.id in Gsub by lia.
  unfold disco_json_reader_model.tv_text.
  rewrite skipn_app, firstn_app in Gsub.
  replace (Z.to_nat (snd t) - length (skipn (Z.to_nat (snd (fst t))) X))%nat with 0%nat in Gsub
    by (rewrite length_skipn; lia).
  cbn [firstn] in Gsub. rewrite app_nil_r in Gsub. exact Gsub. }
assert (HOOc : garr8 SEGS (rd W memc) (d_obj cx OO)
  (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))).
{ assert (LOSn : (length (slot_ser_defs.objs_bytes buf vpad os) = 144 * Z.to_nat count)%nat)
    by (rewrite (slot_ser_Pq.objs_len buf vpad os HVP H6); f_equal; exact Los).
  assert (LOO : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)))
    = 144 * count) by (rewrite length_map, LOSn; lia).
  apply KG; [unfold d_obj, dobj_off; lia | rewrite LOO; unfold d_obj, dobj_off; lia |
    intros x Hx; rewrite LOO in Hx; unfold d_obj, dobj_off in Hx; lia | exact HOO]. }
pose proof (pfxa_slot01 _ _ buf vpad os HVP H6 Hlos HOOc) as HSL. fold t in HSL.
destruct (pfxa_slot_vals _ _ buf vpad t HVP ltac:(lia) HSL ltac:(lia) ltac:(lia) ltac:(lia)) as (Mvp & Mvn & Mvk).
unfold d_obj, dobj_off in Mvp, Mvn, Mvk.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat
  (YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 1664 1668
     (YP09.mkChunk 1664 (CVal 4 (SLit 1)) :: dfhdr_chunks ++ [YP09.mkChunk 2168 (CVal 4 (SLit 2))]))
  HSpi eq_refl) as HR516.
assert (HG1664 : garr8 SEGS (rd W memc) (d_obj cx OUSED) [1; 0; 0; 0]).
{ pose proof (Forall_inv (proj2 (proj2 (proj2 HR516)))) as HC1.
  cbn [YP09.r_base base_val] in HC1. rewrite d_env_old in HC1 by (cbv; lia).
  change 516%nat with AT_F in HC1. rewrite HFU in HC1.
  pose proof (ReacHuntPin.pin_garr8_le4 SEGS (d_env cx E (a3f_vals regs)) (rd W memc) (d_FB cx) 1664
    (SLit 1) (Z_to_bv 64 1) HC1 eq_refl) as HG0.
  replace (map (fun b : byte => bv_unsigned b) (Mem.le4 (Z_to_bv 64 1))) with [1; 0; 0; 0] in HG0
    by (vm_compute; reflexivity).
  unfold d_obj, dobj_off. exact HG0. }
assert (HMCin : In (McConsts.MC_CONSTS_LO, 32) disco_ro_ranges).
{ unfold disco_ro_ranges. apply in_or_app. right. cbn. repeat (first [left; reflexivity | right]). }
replace (d_FB cx + 240 + 24) with (d_FB cx + 264) in Mvp, Mvn, Mvk by lia.
assert (HMCro : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a).
{ intros a Ha. apply (disco_ro_in_ro _ _ a (in_or_app _ _ _ (or_introl HMCin))).
  unfold McConsts.MC_CONSTS_LO, McConsts.MC_CONSTS_HI in Ha |- *. lia. }
assert (HMCun : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. apply (disco_ro_unowned_at B _ _ DRO HMCin a).
  unfold McConsts.MC_CONSTS_LO, McConsts.MC_CONSTS_HI in Ha |- *. lia. }
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W memc mdc k HCTXc)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpresc & GSHc & GSTKc & _ & _ & _ & _).
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
pose proof (pa_img_range xk (KIMG xk ltac:(lia))) as XR. unfold IMG_LO, IMG_TOP in XR.
assert (Ltxt : (length txt <= 7)%nat) by (unfold txt; cbv; lia).
assert (Lsl : (length sl <= 7)%nat) by (rewrite Hsl; pose proof (Z.mod_pos_bound (- (xk + Z.of_nat (length txt) + 1)) 8 ltac:(lia)); lia).
eapply SRr_bind; [apply (aj_jtok_at B LAWS TJTOK fq W R memc LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 mdc k (d_A cx - d_S cx) (d_FB cx + 264) xk 1 1
    (buf + snd (fst t)) (snd t) (printf_facts_c.pf_bytes txt) sl
    (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)) HJ) |].
- rewrite SpR. lia.
- lia.
- lia.
- rewrite Htk. unfold LLVMF_STK. lia.
- rewrite Q3. exact Rgp.
- rewrite Q4. exact Rtp.
- rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
- unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
- exact HIMGc.
- exact (mc_cv_ok B W memc HMCro HMCun HIMGc).
- exact Q10.
- exact Q11.
- exact Q12.
- lia.
- lia.
- lia.
- lia.
- lia.
- exact Mvp.
- exact Mvn.
- change (1 mod 2 ^ 32) with 1. rewrite <- HRk. exact Mvk.
- lia.
- lia.
- apply (amem_range_sub_app (d_FB cx) 4096); [exact GFapp | lia | lia | lia | lia].
- exact (pfxa_tok_ra cx W memc HSHDc ltac:(lia) ltac:(lia)).
- exact (pfxa_tok_hull cx W memc GSHc GF32 ltac:(lia)).
- left. rewrite SpR, Htk. lia.
- exact (slot_ser_Pq.pf_no_zero txt KF).
- exact KG2.
- rewrite HTL, Hsl. rewrite Z2Nat.id; [lia | apply Z.mod_pos_bound; lia].
- exact Kx0.
- rewrite HTL. lia.
- rewrite HTL. lia.
- rewrite HTL. replace (Z.of_nat (length txt + 1)) with (Z.of_nat (length txt) + 1) by lia. exact KAM.
- rewrite HTL. replace (Z.of_nat (length txt + 1)) with (Z.of_nat (length txt) + 1) by lia. exact KRA.
- rewrite HTL. replace (Z.of_nat (length txt + 1)) with (Z.of_nat (length txt) + 1) by lia. exact KSH.
- left. rewrite SpR, Htk, HTL. lia.
- intros _ _.
  assert (LP : length (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)) =
    length (printf_facts_c.pf_bytes txt)) by (rewrite HRT3; reflexivity).
  rewrite LP, HTL.
  split; [reflexivity|]. split; [exact HPG|]. split; [lia|]. split; [lia|].
  split; [exact PAM|]. split; [exact PRA|]. split; [exact PSH|].
  left. rewrite SpR, Htk. lia.
- intros W2 c2 HW2 (fq2 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hcsr2 & HJ4 & HJc & HP4 & HPerm & HKeep & Hres).
  assert (HXb : Forall (fun cc => 0 <= cc < 256) X) by (eapply Forall_impl; [|exact Hg33]; intros cc Hcc; cbv beta in Hcc; lia).
  pose proof (proj2 (slot_ser_Pq.jt_iff X t 1 txt HXb KF ltac:(lia)) HRT) as HM. rewrite HRk in HM.
  assert (R10 : getr regs4 10 = w64 1) by (destruct Hres as [(_ & H10) | (Hn10 & _)]; [exact H10 | contradiction]).
  rewrite SpR, Htk in HKeep.
  pose proof HJc as (_ & _ & _ & _ & _ & HfrC & _).
  assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFRS).
  assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR4)).
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 k HCTX4)
    as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
  destruct HFRMc as (E2 & HdE2 & HREG2 & HFLAG2 & _ & _).
  pose proof HdE2 as (HER2 & HE322 & HEI2 & HEA2 & HEF2 & HESH2).
  assert (HEId2 : img_env VAL A_LIM (d_env cx E2 (map (getr R) (tl all_regs))))
    by (apply img_env_havoc_hi; [exact HEI2 | unfold AT_FL, A_LIM; lia]).
  pose proof (DSEAT LAWS PAL fq2 cx dsh_ser2 ly3 S3 W R memc mdc k E2 AF_jtok_is
    (SLit 0 :: SOff A_TEXT 8104 :: atom_regs 532 30) (map (getr R) (tl all_regs)) [] [] [] (d_facts [] [])
    HCTXc HdE2 HREG2 HFLAG2 (pfxa_regs2 cx E2 R HEI2 Q1)
    (DFACTS LAWS cx ly3 S3 W memc mdc k E2 (map (getr R) (tl all_regs)) [] [] HCTXc HdE2 I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HSC.
  jafter_call_keep_hi HSC 562%nat regs4 (mrestrict (w_H W2) mem4) HP4 [0;1;2;3]%nat HS2.
  match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
  { cbn [ms_mem restrict YK11.mkst]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (d_S cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). rewrite (HER2 2%nat 2%bv eq_refl). reflexivity.
      + intros a Ha. apply HKeep; lia.
      + intros a Ha. lia.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (d_A cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite HEA2. unfold w64.
        apply unsigned_lit_small. lia.
      + intros a Ha. apply HKeep; lia.
      + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (d_FB cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite HEF2. unfold w64.
        apply unsigned_lit_small. lia.
      + intros a Ha. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. apply HKeep; lia.
      + intros a Ha. apply GFpres4. unfold DFRAME_SIZE in Ha. lia.
    - eapply (pfxa_kept _ (w_H W) (w_H W2) memc mem4 _ (shadow_addr (d_FB cx))).
      + rewrite d_env_old by (unfold AT_FL; lia). change 529%nat with AT_SH. rewrite HESH2. unfold w64.
        apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia.
      + intros a Ha. apply HKeep; unfold shadow_addr, SHADOW_OFF in *; lia.
      + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
        apply GFsh4. lia. }
  specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
  assert (HE3 : d_E cx (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
    by (apply pfxa_dE; [apply d_E_env; exact HdE2 | lia]).
  assert (HFL3 : ew (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
    Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
    by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
  assert (HEI3 : img_env VAL A_LIM (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
    by (apply img_env_havoc_hi; [exact HEId2 | unfold A_LIM; lia]).
  pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 1 HS2 ltac:(cbn [ms_regs restrict YK11.mkst]; exact R10) eq_refl)
    as HS3.
  clear HS2.
  pose proof (st_ok_pi_submem _ _ _ _ HS3 (pfxa_narrow0_sub _) ltac:(vm_compute; reflexivity)) as HS4.
  clear HS3. cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS4. norm_ss HS4.
  rewrite Q1.
  pose proof HJ4 as HJ4c.
  clear HF HFr HG.
  pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq2) B LAWS).
  paj_run_to_shc RUNTOP HS4 HJ4 R1_OFF.
  + lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil.
  + assert (Emem : ms_mem ms0 = mem4).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hr & Hw).
      vm_compute in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia|]). destruct Hr. }
    pmkst HS4.
    prreg HS4 (2%bv : bv 5) F2. prreg HS4 (3%bv : bv 5) F3. prreg HS4 (4%bv : bv 5) F4. prreg HS4 (8%bv : bv 5) F8.
    prreg HS4 (9%bv : bv 5) F9. prreg HS4 (18%bv : bv 5) F18. prreg HS4 (20%bv : bv 5) F20.
    prreg HS4 (24%bv : bv 5) F24. prreg HS4 (25%bv : bv 5) F25. prreg HS4 (26%bv : bv 5) F26.
    assert (KV4 : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat nb -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668) /\ ~ (d_A cx - 8240 <= x < d_A cx)) ->
      val_mem SEGS (rd W mem3) a nb v -> val_mem SEGS (rd W2 mem4) a nb v).
    { intros a nb v Ha Hb Hx Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
      intros kk Hkk. destruct (Hx (a + kk) ltac:(lia)) as (Hx1 & Hx2).
      rewrite (HKeep (a + kk) ltac:(lia) Hx2). apply KC; [lia | exact Hx1]. }
    assert (KG4 : forall a L, 0 <= a -> a + Z.of_nat (length L) <= 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat (length L) -> ~ (d_FB cx + 1664 <= x < d_FB cx + 1668) /\ ~ (d_A cx - 8240 <= x < d_A cx)) ->
      garr8 SEGS (rd W mem3) a L -> garr8 SEGS (rd W2 mem4) a L).
    { intros a L Ha Hb Hx Hv. eapply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
      intros x Hx'. destruct (Hx x Hx') as (Hx1 & Hx2).
      rewrite (HKeep x ltac:(lia) Hx2). apply KC; [lia | exact Hx1]. }
    assert (H216f : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 216) 8 h)
      by (rewrite Emem; apply KV4; [lia | lia | intros x Hx; split; lia | exact H216]).
    assert (H152f : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 152) 8 (h + 440))
      by (rewrite Emem; apply KV4; [lia | lia | intros x Hx; split; lia | exact H152]).
    assert (HCTXf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 (ms_mem ms0)
      (with_vm_backing (m_vm_lazy md4) mat0 md4) k) by exact (conj HBASE (conj HJ4 HFR4)).
    pose proof (DLAND LAWS FFL fq2 cx h dsh_ser2 ly4 S4 W2 (with_vm_backing (m_vm_lazy md4) mat0 md4) k
      (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) _ ms0 HCTXf HE3 HFL3 HS4
      ltac:(vm_compute; reflexivity) H216f H152f) as (HFRMf & HSHDf).
    rewrite Emem in HFRMf, HSHDf, HJ4.
    pose proof (d_body_call_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W memc
      ly4 S4 W2 mem4 md4 k (d_A cx - 8240) (d_A cx) HBODYc (conj HBASE HJ4c) ltac:(unfold LLVMF_STK; lia) ltac:(lia)
      ltac:(intros a Ha Hna; exact (HKeep a Ha Hna)) HPerm HFRMf HSHDf) as HBODYf.
    assert (F2' : getr (ms_regs ms0) 2 = getr R 2)
      by (rewrite F2; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 1 ltac:(rewrite length_map; cbn; lia))).
    assert (F3' : getr (ms_regs ms0) 3 = getr R 3)
      by (rewrite F3; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 2 ltac:(rewrite length_map; cbn; lia))).
    assert (F4' : getr (ms_regs ms0) 4 = getr R 4)
      by (rewrite F4; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 3 ltac:(rewrite length_map; cbn; lia))).
    assert (F8' : getr (ms_regs ms0) 8 = getr R 8)
      by (rewrite F8; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 7 ltac:(rewrite length_map; cbn; lia))).
    assert (F9' : getr (ms_regs ms0) 9 = getr R 9)
      by (rewrite F9; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 8 ltac:(rewrite length_map; cbn; lia))).
    assert (F18' : getr (ms_regs ms0) 18 = getr R 18)
      by (rewrite F18; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 17 ltac:(rewrite length_map; cbn; lia))).
    assert (F20' : getr (ms_regs ms0) 20 = getr R 20)
      by (rewrite F20; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 19 ltac:(rewrite length_map; cbn; lia))).
    assert (F24' : getr (ms_regs ms0) 24 = getr R 24)
      by (rewrite F24; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 23 ltac:(rewrite length_map; cbn; lia))).
    assert (F25' : getr (ms_regs ms0) 25 = getr R 25)
      by (rewrite F25; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 24 ltac:(rewrite length_map; cbn; lia))).
    assert (F26' : getr (ms_regs ms0) 26 = getr R 26)
      by (rewrite F26; exact (d_env_x cx E2 (map (getr R) (tl all_regs)) 25 ltac:(rewrite length_map; cbn; lia))).
    assert (HU1 : garr8 SEGS (rd W2 mem4) (d_obj cx OUSED) (a3f_used 1)).
    { assert (EU1 : a3f_used 1 = [1; 0; 0; 0] ++ skipn 4 (a3f_used 0)) by (vm_compute; reflexivity).
      rewrite EU1. apply garr8_app. split.
      - apply (garr8_aview_kept SEGS (w_H W) (w_H W2) memc mem4 (d_obj cx OUSED) [1;0;0;0]); [|exact HG1664].
        intros x Hx. cbn [length] in Hx. apply HKeep; unfold d_obj, dobj_off in *; lia.
      - cbn [length].
        assert (HT0 : garr8 SEGS (rd W mem3) (d_obj cx OUSED + 4) (skipn 4 (a3f_used 0))).
        { rewrite <- (firstn_skipn 4 (a3f_used 0)) in HUSED.
          apply garr8_app in HUSED as [_ HUt].
          replace (length (firstn 4 (a3f_used 0))) with 4%nat in HUt by (vm_compute; reflexivity).
          exact HUt. }
        apply KG4; [unfold d_obj, dobj_off; lia | | | exact HT0];
          replace (length (skipn 4 (a3f_used 0))) with 28%nat by (vm_compute; reflexivity);
          [|intros x Hx; split]; unfold d_obj, dobj_off in *; lia. }

    rewrite Emem.
    apply SRr_ret.
    unfold f_r1, a3f_st. split.
    { destruct HFROM as (HA3 & HW0 & HL0 & HEX). split; [exact HA3|].
      split; [eapply wle_trans; [exact HW0 | exact HW2]|]. split; [exact HL0 | exact HEX]. }
    unfold d_arm_at_pf, d_at.
    exists fq2, ly4, S4, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), k, acc.
    split; [unfold cfg_at, w64, R1_OFF; reflexivity|].
    split; [destruct Hcsr2 as [Hcs | Hcs]; [rewrite Hcs; assumption | exact Hcs]|]. split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|]. split; [exact Hk|].
    split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
    split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
    split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
    pose proof HSP1 as ((H232 & H344) & H224 & H248).
    split.
    { split; [unfold spZ; rewrite F2'; exact SpR|].
      split; [rewrite F3', Q3; exact Rgp|]. split; [rewrite F4', Q4; exact Rtp|].
      split; [rewrite F8', Q8; unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
      split; [rewrite F9'; exact Q9|]. split; [rewrite F18'; exact Q18|].
      split; [rewrite F20'; exact Q20|]. rewrite F25'; exact Q25. }
    split.
    { split; [rewrite F26', Q26; exact R26|]. rewrite F24', Q24. unfold w64, d_obj, dobj_off. f_equal. lia. }
    split.
    { split.
      { split; [split|split].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H232].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H344].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H224].
        - apply KV4; [lia | lia | intros x Hx; split; lia | exact H248]. }
      split.
      { split; [exact (proj1 HTAB)|].
        apply KG4; [unfold d_obj, dobj_off; lia | | | exact HOT];
          rewrite length_map, LT1; [|intros x Hx; split]; unfold d_obj, dobj_off in *; lia. }
      split.
      { split; [exact HBr|].
        apply KG4; [lia | | | exact HBG]; rewrite length_app; cbn [length];
          [|intros x Hx; split]; lia. }
      split; [exact HJR|]. split; [exact HVP|].
      split.
      { assert (LOSn : (length (slot_ser_defs.objs_bytes buf vpad os) = 144 * Z.to_nat count)%nat)
          by (rewrite (slot_ser_Pq.objs_len buf vpad os HVP H6); f_equal; exact Los).
        assert (LOO : Z.of_nat (length (map (fun b : byte => bv_unsigned b)
          (slot_ser_defs.objs_bytes buf vpad os))) = 144 * count) by (rewrite length_map, LOSn; lia).
        apply KG4; [unfold d_obj, dobj_off; lia | rewrite LOO; unfold d_obj, dobj_off; lia |
          intros x Hx; rewrite LOO in Hx; unfold d_obj, dobj_off in Hx; split; lia | exact HOO]. }
      split.
      { split; [exact Hpc|].
        split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H368]|].
        apply KV4; [lia | lia | intros x Hx; split; lia | exact H336]. }
      split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H392]|].
      split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H408]|].
      exact HU1. }
    split.
    { split; [apply KV4; [lia | lia | intros x Hx; split; lia | exact H232]|].
      apply KV4; [lia | lia | intros x Hx; split; lia | exact H344]. }
    exact HBODYf.
}
Qed.


End h.
End f.
End d.
