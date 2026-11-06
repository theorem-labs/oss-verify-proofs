(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module paths and module names changed; 518 of its 589 lines of code are new or changed and 1621 lines of the source are left out. *)
(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the arm's first two steps.
   - wvc_entry_step: from write_value_spec_at's premises (FSW_write_value.wv_spec_on's, the arm's node header in place
     of the tree class) through the entry run (ZZwv_runs1.wvc_seg_entry) and the call of put with the opening literal
     ('[' at 0x21180 / '{' at 0x21160) to the OPEN point WVC_R_OPEN (ZZwv_inv.wvc_invO).
   - wvc_open_ind_step: from the OPEN point with n <> 0 through ZZwv_runs1.wvc_seg_open_ind and the call of indent
     (pretty, d + 1) to the first item's R_IND point (ZZwv_inv.wvc_inv at item 0).
   Rule 24: no function proved here (segments of write_value's container arms; the lane's lookup for write_value,
   CHECKER CONFIRM a Theorem Labs lane, is recorded in (internal path)). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_comp ZZwv_tree ZZwv_call ZZwv_call2
ZZwv_call3 ZZwv_res ZZwv_ret ZZwv_runs2 ZZwv_runs1 ZZwv_step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x FSW_write_value.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* a list membership found by trying each element *)
Ltac wvc_inl := repeat (first [left; reflexivity | right]).

(* a code address as a return address *)
Lemma wvc_ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 z).
Proof. intros z Hz He. apply YK0s.ret_ok_even. rewrite unsigned_lit_small by lia. exact He. Qed.

(* the shadow address of the entry node (atom 11), as ZZwv_step.wvc_shv_U computes it for atom 9 *)
Lemma wvc_shv_U11 : forall E c v, ew E 11 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= v + c -> v + c < 2 ^ 60 -> 0 <= v < 2 ^ 64 ->
  U E (wvc_shv 11 c) = (v + c) / 8 + SHADOW_OFF.
Proof.
intros E c v H11 H32 H0 H1 Hv. unfold wvc_shv.
rewrite U_SAlu, U_SAlu, U_SOff, U_SOff, U_SLit, H11, H32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small (v + c)) by lia. rewrite (Z.mod_small 3) by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((v + c) / 8)) by lia. rewrite Z.add_0_r, (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.

(* the 32-bit type field of a node names one type *)
Lemma wvc_u32_uniq : forall m a x y,
  PjStruct.pj_u32 tfibsegs m a x -> PjStruct.pj_u32 tfibsegs m a y -> x = y.
Proof.
intros m a x y (Hx & Bx) (Hy & By).
pose proof (PjStruct.pj_bytes_uniq tfibsegs m a _ _ Bx By ltac:(rewrite !Mem.length_le4; reflexivity)) as E.
apply (f_equal bytes_le_to_Z) in E. rewrite !Mem.bytes_le_to_Z_le4, !unsigned_lit_small in E by lia.
rewrite !Z.mod_small in E by lia. exact E.
Qed.

(* the opening literal of a container: one byte of fs's read-only strings *)
Lemma wvc_open_lit : forall ty, ty = 5 \/ ty = 6 ->
  In (wvc_open ty, if ty =? 6 then [123] else [91]) FS_RO_STRS /\ 0 <= wvc_open ty /\ wvc_open ty + 1 <= SHADOW_OFF.
Proof.
intros ty [-> | ->]; (split; [unfold FS_RO_STRS; wvc_inl | unfold wvc_open, WVC_LBRACE, WVC_LBRACKET, SHADOW_OFF; cbn; lia]).
Qed.

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- the word at sp - 8 is the entry ra: write_value's frame slot 168 (wvc_cs0, atom xatom 17) ---- *)
Lemma wvc_ra_slot : forall ly S U (W : world tfibsegs) m md R regs str kids keys n d ke key sp,
  ARU tfibsegs B ly S U W m md ->
  Forall (YP09.chunk_ok tfibsegs (Ereg R (fs_extraT ++ wvc_xs regs str kids keys n d ke key))
            (mrestrict (w_H W) m) (sp - WVC_F)) wvc_cs0 ->
  alloc_ceiling <= sp - WVC_F -> sp <= 2 ^ 47 ->
  rdword (aview tfibsegs (w_H W) (unpoison U m)) (sp - 8) = Some (raZ regs).
Proof.
intros ly S U W m md R regs str kids keys n d ke key sp HARU HC Hlo Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (YP09.mkChunk 168 (CVal 8 (SOff (xatom 17) 0))) wvc_cs0).
{ unfold wvc_cs0. cbn [map seq]. wvc_inl. }
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc.
assert (Hv : val_mem tfibsegs (mrestrict (w_H W) m) (sp - WVC_F + 168) (N.to_nat 8) (raZ regs)).
{ apply (val_of_chunk_ok tfibsegs _ _ _ _ _ _ _ Hc).
  - rewrite fsw_SOff0. change (xatom 17) with (xatom (5 + 12)).
    rewrite (wvr1_xs_saved R regs str kids keys n d ke key 12) by lia. cbn [nth wvc_saved].
    unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - unfold raZ. pose proof (u64_range (getr regs 1)). cbn. lia.
  - cbn. lia. }
replace (sp - WVC_F + 168) with (sp - 8) in Hv by (unfold WVC_F; lia).
pose proof (AF0x.val_mem_rdword (w_H W) m (sp - 8) (raZ regs) ltac:(unfold raZ; apply u64_range) Hv) as Hw.
rewrite (rdword_ext (aview tfibsegs (w_H W) m) (aview tfibsegs (w_H W) (unpoison U m)) (sp - 8)); [exact Hw|].
intros kk Hkk. apply aview_unpoison_out. apply (zwk_p_stack_not_ush B ly S U W m md); [exact HARU | unfold WVC_F in *; lia].
Qed.

(* ---- a read-only literal's bytes below the shadow: the unpoisoned view is the machine's ---- *)
Lemma wvc_lit_raw : forall ly S U (W : world tfibsegs) m md SA (LB : list Z),
  ARU tfibsegs B ly S U W m md -> 0 <= SA -> SA + Z.of_nat (length LB) <= SHADOW_OFF ->
  zbytes_at tfibsegs W (unpoison U m) SA LB -> zbytes_at tfibsegs W m SA LB.
Proof.
intros ly S U W m md SA LB HARU H0 H1 HZ j Hj. destruct (HZ j Hj) as (Hv & Hb). split; [|exact Hb].
intros kk Hkk. etransitivity; [|exact (Hv kk Hkk)].
unfold mbyte. rewrite (zwk_j_mrestrict_low B ly S U W m md (w_H W)) by (exact HARU || lia).
reflexivity.
Qed.

End H.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis HSS : FsShadowSyms B.
(* the arm instance: its fixed data and the entry state *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
(* the entry facts the arms' callers discharge once *)
Hypothesis HE_sp16 : wf_sp F mod 16 = 0.
Hypothesis HE_ot16 : wf_ot F mod 16 = 0.
Hypothesis HE_oot : wf_o F + 32 <= wf_ot F.
Hypothesis HE_o8 : wf_o F mod 8 = 0.
Hypothesis HE_top : wf_ot F <= ly_top ly0.
Hypothesis HE_top47 : ly_top ly0 <= 2 ^ 47.
Hypothesis HE_lo : alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F.
Hypothesis HE_gp : YK11.getr regs0 3%bv = w64 (as_gp B).
Hypothesis HE_tp : YK11.getr regs0 4%bv = w64 (as_tp B).
Hypothesis HE_cap0 : 0 <= wf_cap0 F.
Hypothesis HE_capl : wf_cap0 F <= wf_live F.
Hypothesis HE_cnt0 : 0 <= wf_cnt0 F.
Hypothesis HE_p : 0 <= wf_p F < alloc_ceiling.
Hypothesis HE_d : 0 <= wf_d F.
Hypothesis HE_dd : wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1.
Hypothesis HE_room : Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX.
Hypothesis HE_bud : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)).
Hypothesis HE_frl : Z.of_nat (length (frames S0)) <= FRL_CRT_CALLEE.
Hypothesis HE_foot : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x.
Hypothesis HE_plain : jv_plain (wf_t F).
Hypothesis HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members)).
Hypothesis HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W0 mem0) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Hypothesis HE_n : 0 <= wf_n F < 2 ^ 54.
Hypothesis HE_kk : 0 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling.

(* ================= (1) the entry: to the OPEN point ================= *)
Lemma wvc_entry_step : forall ly S U (W : world tfibsegs) regs mem md ch ot o v pretty d (t : PjTree.jv) D UL buf cap
    failed text live peak cnt fail ty num str kids keys n cap0 slo shi k ra8 (Q : world tfibsegs -> config -> Prop),
  put_spec B tfibsegs ->
  fs_img_facts tfibsegs B ->
  F = mkWF ty pretty d ot o v str kids keys n buf cap failed text live peak cnt fail UL D t ra8 (spZ regs) (2 - k) ->
  rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra8 ->
  ty = 5 \/ ty = 6 ->
  PjStruct.pj_hdr tfibsegs (rdW W mem) v ty num str kids keys n cap0 /\ slo <= str <= shi ->
  (PjTree.depth t <= 2 - k)%nat ->
  fpreU tfibsegs B (STK_write_value (2 - k)) ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 d ->
  0 <= pretty < alloc_ceiling -> 0 <= d < 2 ^ 31 -> d + Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
  (s0Z regs < alloc_ceiling \/ s0Z regs = o \/ o + 48 <= s0Z regs) ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  FSW_write_value.wv_chain_o U W mem regs o ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  PjStruct.pj_node tfibsegs (rdW W mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  ublocks_ok B tfibsegs ly S W mem UL -> (forall a k, In (a, k) D -> In (a, k) UL /\ a <> buf) ->
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) ->
  jv_plain t ->
  (forall x, o <= x < ot -> ~ PjStruct.pj_foot v D x) ->
  Z.of_nat (length text)
    + Z.of_nat (length (concat (WriterValue.wvpieces t (negb (pretty =? 0)) d))) + 1 <= WMAX ->
  cap <= WMAX -> cap <= live ->
  wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterValue.wvpieces t (negb (pretty =? 0)) d)) ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf',
     wvc_invO B F ly S U W mem md regs W' (mkst regs' (Z_to_bv 64 WVC_R_OPEN) mem' (seg_rom tfibsegs)) md'
       ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_OPEN regs' mem' md') Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_write_value regs mem md) Q.
Proof.
intros ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail ty num str kids keys n
  cap0 slo shi k ra8 Q HPUT IMG HF H8 Hty (HH & Hs) Hdep HPRE HHEADS HFRL G10 G11 G12 G13 Hpr Hd Hdd HS0w HOUT HGLOB
  HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot Hplain Hfoot HROOM HCAP HCL HBUD K.
clear HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo HE_gp HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room
  HE_bud HE_frl HE_foot HE_plain HE_ty HE_hdr HE_n HE_kk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
(* the arm's fixed data *)
assert (Fty : wf_ty F = ty) by (rewrite HF; reflexivity).
assert (Fp : wf_p F = pretty) by (rewrite HF; reflexivity).
assert (Fd : wf_d F = d) by (rewrite HF; reflexivity).
assert (Fot : wf_ot F = ot) by (rewrite HF; reflexivity).
assert (Fo : wf_o F = o) by (rewrite HF; reflexivity).
assert (Fv : wf_v F = v) by (rewrite HF; reflexivity).
assert (Fstr : wf_str F = str) by (rewrite HF; reflexivity).
assert (Fkids : wf_kids F = kids) by (rewrite HF; reflexivity).
assert (Fkeys : wf_keys F = keys) by (rewrite HF; reflexivity).
assert (Fn : wf_n F = n) by (rewrite HF; reflexivity).
assert (Fbuf : wf_buf0 F = buf) by (rewrite HF; reflexivity).
assert (Fcap : wf_cap0 F = cap) by (rewrite HF; reflexivity).
assert (Ffailed : wf_failed0 F = failed) by (rewrite HF; reflexivity).
assert (Ftext : wf_text0 F = text) by (rewrite HF; reflexivity).
assert (Flive : wf_live F = live) by (rewrite HF; reflexivity).
assert (Fpeak : wf_peak0 F = peak) by (rewrite HF; reflexivity).
assert (Fcnt : wf_cnt0 F = cnt) by (rewrite HF; reflexivity).
assert (Ffail : wf_fail0 F = fail) by (rewrite HF; reflexivity).
assert (FUL : wf_UL F = UL) by (rewrite HF; reflexivity).
assert (FD : wf_D F = D) by (rewrite HF; reflexivity).
assert (Ft : wf_t F = t) by (rewrite HF; reflexivity).
assert (Fra8 : wf_ra8 F = ra8) by (rewrite HF; reflexivity).
assert (Fsp : wf_sp F = spZ regs) by (rewrite HF; reflexivity).
assert (Fm : wf_m F = (2 - k)%nat) by (rewrite HF; reflexivity).
assert (Est0 : wvc_st0 F = WriterApp.mkW failed text cap cnt fail []).
{ unfold wvc_st0. rewrite Ffailed, Ftext, Fcap, Fcnt, Ffail. reflexivity. }
(* the entry's machine facts *)
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & Htop & Htop2).
destruct (fsw_sp B _ ly S U W regs mem md ch HPREU) as (Hsp16 & Hceil & Hsp47 & _).
pose proof (wvc_stk (2 - k)) as (HSF & HSput & _ & _ & _).
assert (SKp0 : 0 <= STK_put) by (vm_compute; discriminate).
destruct (fsw_pobj_low B ly S W _ md mem v HAR HPO) as (Hv1 & Hv2).
pose proof HOUT as (Ho8 & Ho0 & Hotop & _ & Hbuf64 & Hcap64 & _ & _ & _ & _ & _ & _ & Hcase).
assert (Hbin : cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)).
{ intros Hc0. destruct Hcase as [(Hz & _) | (_ & (Hb & _) & _)]; [exfalso; exact (Hc0 Hz) | exact Hb]. }
assert (Hb0 : cap = 0 -> buf = 0).
{ intros Hz. destruct Hcase as [(_ & E & _) | ((j & Hj & Ej) & _)]; [exact E|].
  exfalso. rewrite Ej in Hz. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)). lia. }
pose proof HGLOB as (_ & _ & _ & _ & Hlp & _ & Hcnt64 & _).
(* the tree is the container the header names *)
assert (Htag : PjTree.tag t = ty).
{ assert (Hh : exists num' str' kids' keys' n' cap',
    PjStruct.pj_hdr tfibsegs (rdW W mem) v (PjTree.tag t) num' str' kids' keys' n' cap').
  { destruct t; cbn [PjStruct.pj_node] in HN;
      destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & HH' & _);
      exists num', str', kids', keys', n', cap'; exact HH'. }
  destruct Hh as (num' & str' & kids' & keys' & n' & cap' & (_ & HT' & _)).
  destruct HH as (_ & HT & _).
  exact (wvc_u32_uniq _ _ _ _ HT' HT). }
set (lb := if ty =? 6 then [123] else [91]).
assert (HWV : exists Rest, WriterValue.wvpieces t (negb (pretty =? 0)) d = [lb] ++ Rest).
{ destruct t; cbn [PjTree.tag] in Htag;
    try (exfalso; destruct Hty as [Hx | Hx]; rewrite <- Htag in Hx; discriminate Hx);
    eexists; unfold lb; rewrite <- Htag; reflexivity. }
destruct HWV as (Rest & HWV).
assert (Hlb : length lb = 1%nat) by (unfold lb; destruct (ty =? 6); reflexivity).
assert (Hlbty : (if wf_ty F =? 6 then [123] else [91]) = lb) by (rewrite Fty; reflexivity).
destruct (wvc_open_lit ty Hty) as (HLin & HSA0 & HSAsh).
assert (Hroom : Z.of_nat (length text) + 1 + 1 <= WMAX).
{ rewrite HWV, concat_app, length_app in HROOM. cbn [concat] in HROOM. rewrite app_nil_r, Hlb in HROOM. lia. }
assert (HBUD1 : wbudget_pre S cap cnt live (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) [lb])).
{ rewrite HWV in HBUD. exact (wv_budget_pre_prefix S cap cnt live failed text fail [lb] Rest ltac:(lia) HBUD). }
(* the entry state, the journal from the entry, ARU *)
destruct (FSW_write_value.wv_start B HSS IMG k ly S U W regs mem md ch ot v ty num str kids keys n cap0 slo shi buf cap
  HPRE G11 HPO HH Hs ltac:(lia) Hot16 Hottop HPRESENT) as (HS & SHOK & HJ & HARU & E2).
unfold cfg_at. change (w64 A_write_value) with (Z_to_bv 64 A_write_value).
(* the entry run, to put of the opening literal *)
eapply (wvc_seg_entry B W (mkst regs (Z_to_bv 64 A_write_value) mem (seg_rom tfibsegs)) md regs ty slo shi str kids keys
  n (STK_write_value (2 - k)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md [] ly S U 0 Q).
{ split; [exact HS|]. split; [exact SHOK|]. split; [exact HJ | exact HARU]. }
{ exact Hty. }
{ lia. }
{ exact HSF. }
intros ms' mdc' HJ1 HARU1 HFR1 HCS0 R1 R10 R11 R12 R2 R8 R9 R19 R23 R27 RK Ems'.
rewrite Ems'.
set (regsC := ms_regs ms') in *. set (memC := ms_mem ms') in *.
assert (EspC : spZ regsC = spZ regs - WVC_F) by (unfold spZ at 1; rewrite R2; apply wz; lia).
assert (Hs0C : s0Z regsC = o) by (unfold s0Z; rewrite R8, G10; unfold w64; apply wz; lia).
assert (HraC : raZ regsC = WVC_R_OPEN) by (unfold raZ; rewrite R1; unfold w64; apply wz; unfold WVC_R_OPEN; lia).
(* the writer facts at the entry, then at the call *)
assert (HSEM0 : wvc_sem B F ly S U W mem regs ly S U W mem buf (wvc_st0 F)).
{ rewrite Est0. unfold wvc_sem.
  cbn [WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt WriterApp.w_fail].
  rewrite ?Fo, ?Fcap, ?Fpeak, ?Flive, ?Fbuf, ?Fcnt, ?Ffailed, ?Fsp, ?Fot, ?FUL, ?Fv, ?Ft, ?FD, ?Fra8.
  split; [exact HOUT|].
  split; [exists peak; split; [lia|]; replace (live + cap - cap) with live by lia; exact HGLOB|].
  split; [exact HHEADS|].
  split; [left; split; reflexivity|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [unfold wbudget_kept; split; [exact HCAP | split; lia]|].
  split; [unfold wcalls; cbn [WriterApp.w_calls length Z.of_nat]; lia|].
  split; [intros a _ _; split; [reflexivity | tauto]|].
  split; [exact HN|]. split; [exact HPO|]. split; [intros x _; reflexivity|].
  split; [intros a kk Hak; exact (HUL a kk (proj1 (HD a kk Hak)))|]. split; [exact HD|]. split; [exact Hroot|].
  split; [exact Hbin|]. split; [exact Hb0|]. split; [exact HRO|]. split; [exact H8|].
  split; [|exact HUH].
  unfold FSW_write_value.wv_chain_o in HCHO.
  destruct HCHO as [HC1 | (H16 & ra & nfp & Hra8 & Hnfp & Hend)]; [left; exact HC1 | right].
  rewrite H8 in Hra8. injection Hra8 as <-.
  split; [exact H16|]. exists nfp. split; [exact Hnfp | exact Hend]. }
assert (HFRm : forall x : word, ~ (wf_sp F - WVC_F <= bv_unsigned x < wf_sp F) -> rdW W memC x = rdW W mem x)
  by (rewrite Fsp; exact HFR1).
pose proof (wvc_sem_run B F ly S U W mem regs ly S U W mem memC mdc' buf (wvc_st0 F) HSEM0 HARU1 HFRm
  ltac:(rewrite Fsp; lia) ltac:(rewrite Fo; lia) ltac:(rewrite Fot; lia)) as HSEMC.
assert (HJ1' : ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly S W (unpoison U mem) md [] ly S W
  (unpoison U memC) mdc' 0).
{ unfold wvc_STK, wvc_FP. rewrite Fm, Fot, Fsp, Fbuf, Fcap. exact HJ1. }
(* put's frame-chain, presence and fpreU at the call *)
assert (HC1 : wf_o F = wf_sp F + 8 ->
  rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8) = Some (raZ regs)).
{ intros _. rewrite Fsp. exact (wvc_ra_slot B ly S U W memC mdc' regs regs str kids keys n d 0 0 (spZ regs) HARU1
    (HCS0 regs d 0 0) ltac:(lia) Hsp47). }
destruct (wvc_callpre B F ly S U W mem md regs ly S U W memC mdc' 0 buf (wvc_st0 F) regsC STK_put HJ1' HARU1 HSEMC HC1
  ltac:(rewrite Fsp; exact EspC) ltac:(rewrite Fsp; exact Hsp16) ltac:(rewrite Fot; exact Hot16)
  ltac:(rewrite Fsp, Fot; lia) SKp0 ltac:(rewrite Fm; exact HSput)
  ltac:(rewrite R1; unfold w64; apply wvc_ret_ok_lit; [unfold WVC_R_OPEN; lia | reflexivity])
  ltac:(rewrite HraC; unfold WVC_R_OPEN; lia)
  ltac:(rewrite (RK 3%bv ltac:(wvc_inl)); exact Hgp) ltac:(rewrite (RK 4%bv ltac:(wvc_inl)); exact Htp)
  ltac:(rewrite Fo; exact Hs0C) ltac:(rewrite Fo, Fot; exact Hoot) ltac:(rewrite Fot; exact Hottop)
  ltac:(rewrite Fo; exact Ho8) ltac:(rewrite Fsp; lia))
  as (ch' & _ & HPREC & HCHC & HPRC).
rewrite Fo in HCHC. rewrite Fot in HPRC.
(* the out-object and the statics at the call *)
pose proof HSEMC as (HOUTC & (peakC & HpkC & HGLC) & _).
assert (HOUTC' : wout_ok B tfibsegs ly S W memC o buf cap failed text).
{ rewrite Est0, Fo in HOUTC. exact HOUTC. }
assert (HGLC' : fs_glob tfibsegs W memC live peakC cnt fail).
{ rewrite Est0, Flive, Fcap in HGLC. cbn [WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail] in HGLC.
  replace (live + cap - cap) with live in HGLC by lia. exact HGLC. }
(* the literal's bytes at the call *)
pose proof HPREC as (_ & HROC).
pose proof (proj1 (zwk_j_arodata_unpoison B ly S U W memC mdc' HARU1) HROC) as HROCu.
destruct (wvc_lit_pre B ly S U W (unpoison U memC) mdc' (wvc_open ty) lb buf IMG (proj1 HARU1) HROCu HLin)
  as (HZu & HBOK & _ & HSA1 & HSA2).
pose proof (wvc_lit_raw B ly S U W memC mdc' (wvc_open ty) lb HARU1 HSA0 ltac:(rewrite Hlb; cbn; lia) HZu) as HZ.
rewrite Hlb in HSA2.
(* put of the opening literal *)
eapply SRr_bind.
{ apply (HPUT ly S U W regsC memC mdc' ch' ot o (wvc_open ty) 1 buf cap failed text lb live peakC cnt fail HPREC HHEADS).
  - lia.
  - rewrite R10. exact G10.
  - exact R11.
  - exact R12.
  - exact HOUTC'.
  - exact HGLC'.
  - exact HUH.
  - lia.
  - exact Hoot.
  - exact Hot16.
  - exact Hottop.
  - exact HCHC.
  - exact HPRC.
  - exact HZ.
  - right; right; right. exists lb. split; [exact HLin | apply Nat.le_succ_diag_r].
  - rewrite Hlb. reflexivity.
  - exact HBOK.
  - cbn in HSA2. split; lia.
  - left. cbn in HSA2. lia.
  - exact Hroom.
  - exact HCAP.
  - exact HCL.
  - exact HBUD1. }
intros W' c' _ (st' & buf' & U' & Est & HUS' & Hwp).
unfold wpost, fpostU in Hwp.
destruct Hwp as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & HOUT' & HBK' & HBS' & HWK' & HGL' & _).
assert (Ecal : WriterApp.putN (wv_rst (wvc_st0 F)) [lb] = st') by (rewrite Est0, Est; reflexivity).
assert (Eall : WriterApp.putN (wvc_st0 F) [lb] = st') by (rewrite Est0, Est; reflexivity).
assert (Hcnt1 : wf_cnt0 F + wcalls (WriterApp.putN (wvc_st0 F) [lb]) < 2 ^ 64).
{ rewrite Fcnt, Est0. pose proof HBUD1 as (_ & _ & _ & H4). exact H4. }
(* the writer facts at the return *)
assert (HPOST : ARU tfibsegs B ly' S' U' W' mem' md' /\
  wvc_sem B F ly S U W mem regs ly' S' U' W' mem' buf' (WriterApp.putN (wvc_st0 F) [lb])).
{ apply (wvc_sem_call B F ly S U W mem regs ly S U W memC mdc' buf (wvc_st0 F) [lb] ly' S' U' W' mem' md' buf'
    (STK_put + (ot - spZ regsC)) (wevk cap st') (spZ regsC) peakC HSEMC HARU1).
  - rewrite Fcap. lia.
  - rewrite Est0. cbn [WriterApp.w_cap]. rewrite Fcap. lia.
  - rewrite Fcnt. lia.
  - exact Hcnt1.
  - rewrite Fsp. lia.
  - rewrite Fo, Fot. exact Hoot.
  - exact HpkC.
  - rewrite Fot, Est0. exact HJc.
  - exact OK'.
  - exact PO'.
  - rewrite Est0. exact HUS'.
  - rewrite Fo, Ecal. exact HOUT'.
  - rewrite Ecal, Est0. exact HBK'.
  - rewrite Ecal, Est0. exact HBS'.
  - rewrite Fot, Fo. exact HWK'.
  - rewrite Fsp. lia.
  - rewrite Ecal, Est0, Flive, Fcap. cbn [WriterApp.w_cap]. destruct HGL' as (pk & Hpk & HG). exists pk.
    replace (live + cap - cap - cap + WriterApp.w_cap st') with (live - cap + WriterApp.w_cap st') by lia.
    replace (live + cap - cap + WriterApp.w_cap st' - cap) with (live + WriterApp.w_cap st' - cap) by lia.
    split; [exact Hpk | exact HG]. }
destruct HPOST as (HARU' & HSEM').
(* the resumed env: the callee-saved registers are the call's *)
set (xs := wvc_xs regs (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F) 0).
set (E' := Ereg regs' (fs_extraT ++ xs)).
assert (Hrs : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs' q = getr regsC q)
  by (intros q Hq; exact (fsw_pres regsC regs' q HP Hq)).
assert (E2' : bv_unsigned (ew E' 2) = wf_sp F - WVC_F).
{ unfold E'. rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl), (Hrs 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])).
  rewrite Fsp. exact EspC. }
assert (E9' : ew E' 9 = Z_to_bv 64 (wf_v F)).
{ unfold E'. rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), (Hrs 9%bv ltac:(apply (wvc_cs_z _ 9); [reflexivity | lia])).
  rewrite R9, G11, Fv. reflexivity. }
assert (E32' : ew E' 32 = Z_to_bv 64 SHADOW_OFF).
{ unfold E'. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (EX' : forall j, ew E' (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E'; apply fsw_ew_xatom).
pose proof HSEM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPO' & HNB' & _).
assert (HHDR' : PjStruct.pj_hdr tfibsegs (rdW W' mem') (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F)
  (wf_n F) cap0).
{ apply (PjStruct.pj_hdr_eq tfibsegs (rdW W mem)); [rewrite Fv, Fty, Fstr, Fkids, Fkeys, Fn; exact HH | exact HNB']. }
destruct (wvc_resume_rs0 B ly' S' U' W' mem' md' E' (wf_ty F) wvc_cs0 (wf_v F) num (wf_str F) (wf_kids F) (wf_keys F)
  (wf_n F) cap0 (wf_sp F) HARU' HPO' HHDR' E2' ltac:(rewrite Fsp; lia) ltac:(rewrite Fsp; lia) E9' E32'
  ltac:(rewrite EX'; reflexivity) ltac:(rewrite EX'; reflexivity) ltac:(rewrite EX'; reflexivity)
  ltac:(rewrite EX'; reflexivity)) as (HRS & HPD & HGF & HSH).
(* the frame chunks at the return *)
assert (HCH' : Forall (YP09.chunk_ok tfibsegs E' (rdW W' mem') (wf_sp F - WVC_F)) wvc_cs0).
{ assert (HC0 : Forall (YP09.chunk_ok tfibsegs E' (rdW W memC) (wf_sp F - WVC_F)) wvc_cs0).
  { unfold E', xs. rewrite Fstr, Fkids, Fkeys, Fn, Fd, Fsp. exact (HCS0 regs' d keys 0). }
  exact (wvc_cs0_after E' E' W W' memC mem' (wf_sp F) (spZ regsC) ot o HC0 HWK' ltac:(rewrite Fsp; lia)
    ltac:(rewrite Fsp; lia) Hoot eq_refl eq_refl (fun _ _ => eq_refl)). }
(* the after-call step *)
assert (HFPSUB : fsw_fp_sub B ly S ly S [] (wvc_FP F) (FS_PSTAT_FP ++ wbuf_fp buf cap)).
{ unfold wvc_FP. rewrite Fbuf, Fcap.
  exact (wv_fp_sub_swap B ly S ly S W (unpoison U memC) mdc' buf cap buf cap (proj1 HARU1)
    (or_introl (conj eq_refl (conj eq_refl eq_refl))) Hbin ltac:(lia) wvc_pstat_img). }
destruct (wvc_after_call2 B (wvc_STK F) (wf_ot F) (wvc_FP F) [] ly S U W W mem md ly S U memC mdc' 0 STK_put
  (FS_PSTAT_FP ++ wbuf_fp buf cap) ot WVC_F regsC ly' S' U' W' regs' mem' md' (wevk cap st') xs wvc_cs0
  [wvc_node (wf_ty F)] wvc_gf0 WVC_R_OPEN (wf_sp F) HSS HJ1' HARU1 HJc HFPSUB OK' PO' HP
  ltac:(rewrite Fsp; exact EspC) ltac:(rewrite HWF; lia) SKp0
  ltac:(unfold wvc_STK; rewrite Fm, Fot, Fsp; lia) ltac:(reflexivity) ltac:(rewrite Fsp; exact Hsp16)
  ltac:(lia) ltac:(rewrite Fot; lia) ltac:(rewrite Fsp, Fot; lia) (wvc_rs0_wf (wf_ty F)) HCH' HRS HPD HGF)
  as (HJ' & HARU'' & HST).
(* the open state *)
assert (E11 : ew (Ereg regs (fs_extraT ++ wv_xs0 str kids keys n)) 11 = Z_to_bv 64 v)
  by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact G11).
assert (E32e : ew (Ereg regs (fs_extraT ++ wv_xs0 str kids keys n)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (R27' : getr regs' 27 = w64 (wf_v F / 8 + SHADOW_OFF)).
{ rewrite (Hrs 27%bv ltac:(apply (wvc_cs_z _ 27); [reflexivity | lia])), R27.
  rewrite (wvc_den_val _ (wvc_shv 11 0) _ (wvc_shv_U11 _ 0 v E11 E32e ltac:(lia) ltac:(lia) ltac:(lia))).
  rewrite Fv, Z.add_0_r. reflexivity. }
assert (HSO : st_ok tfibsegs E' (wvc_ssO (wf_ty F))
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 WVC_R_OPEN) mem' (seg_rom tfibsegs)))).
{ apply (wvc_ssO_ret E' (wf_ty F) _ HST).
  cbn [ms_regs restrict mkst]. rewrite R27'.
  rewrite (wvc_den_val E' (wvc_shv 9 0) _ (wvc_shv_U E' 0 (wf_v F) E9' E32' ltac:(lia) ltac:(lia) ltac:(lia))).
  rewrite Z.add_0_r. reflexivity. }
rewrite R1. apply (K ly' S' U' W' regs' mem' md' buf').
unfold wvc_invO. cbv zeta. rewrite !Hlbty.
split.
{ split; [exact HSO|]. split; [exact HSH|]. split; [|exact HARU''].
  assert (Ek : wevk (wf_cap0 F) (wvc_stP F [lb]) = 0 + wevk cap st').
  { rewrite Fcap. unfold wvc_stP. rewrite Eall. lia. }
  rewrite Ek. exact HJ'. }
split; [exact HSEM'|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 8%bv ltac:(apply (wvc_cs_z _ 8); [reflexivity | lia])), R8, G10, Fo;
  reflexivity|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 9%bv ltac:(apply (wvc_cs_z _ 9); [reflexivity | lia])), R9, G11, Fv;
  reflexivity|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 19%bv ltac:(apply (wvc_cs_z _ 19); [reflexivity | lia])), R19, G12, Fp;
  reflexivity|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 23%bv ltac:(apply (wvc_cs_z _ 23); [reflexivity | lia])), R23, G13, Fd;
  reflexivity|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 3%bv ltac:(apply (wvc_cs_z _ 3); [reflexivity | lia]));
  exact (RK 3%bv ltac:(wvc_inl))|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 4%bv ltac:(apply (wvc_cs_z _ 4); [reflexivity | lia]));
  exact (RK 4%bv ltac:(wvc_inl))|].
split; [cbn [ms_regs mkst]; exact R27'|].
cbn [ms_regs mkst]. unfold spZ. rewrite (Hrs 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])).
rewrite Fsp. exact EspC.
Qed.

(* ================= (2) the OPEN point with n <> 0: the first item's indent ================= *)
Lemma wvc_open_ind_step : forall Rest ly S U (W : world tfibsegs) ms mdc buf (Q : world tfibsegs -> config -> Prop),
  indent_spec B tfibsegs ->
  wvc_WP F = [if wf_ty F =? 6 then [123] else [91]] ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1) ++ Rest ->
  wvc_invO B F ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  wf_n F <> 0 ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf' key',
     wvc_inv B F WVC_R_IND 0 (wf_keys F) key'
       ([if wf_ty F =? 6 then [123] else [91]] ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1))
       ly0 S0 U0 W0 mem0 md0 regs0 W' (mkst regs' (Z_to_bv 64 WVC_R_IND) mem' (seg_rom tfibsegs)) md' ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_IND regs' mem' md') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros Rest ly S U W ms mdc buf Q HIND HWP HO Hn0 K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSF & _ & HSind & _ & _).
assert (SKi0 : 0 <= STK_indent) by (vm_compute; discriminate).
assert (Hd1 : wf_d F + 1 < 2 ^ 31).
{ pose proof HE_dd as Hdd.
  destruct HE_ty as [(_ & items & Ht & _ & _) | (_ & members & Ht & _)];
    rewrite Ht in Hdd; cbn [PjTree.depth] in Hdd; lia. }
unfold wvc_invO in HO. cbv zeta in HO.
set (Pd := [if wf_ty F =? 6 then [123] else [91]]) in *.
set (Pc := WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1)) in *.
set (st := wvc_stP F Pd) in *.
set (E := Ereg (ms_regs ms) (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F)
  (wf_keys F) 0)) in *.
destruct HO as ((HS0 & SHOK & HJ & HARU) & HSEM & R8 & R9 & R19 & R23 & R3 & R4 & R27 & Hsp).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf st HSEM) as Hosp.
pose proof HSEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPO0 & _).
destruct (fsw_pobj_low B ly S W _ mdc (ms_mem ms) (wf_v F) (proj1 HARU) HPO0) as (Hv1 & Hv2).
(* the env's values *)
assert (E2 : bv_unsigned (ew E 2) = wf_sp F - WVC_F).
{ unfold E. rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl). exact Hsp. }
assert (EX : forall j, ew E (xatom j) =
  nth j (wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F) 0) (Z_to_bv 64 0))
  by (intros j; unfold E; apply fsw_ew_xatom).
assert (E8 : ew E 8 = Z_to_bv 64 (wf_o F)) by (unfold E; rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 (wf_v F)) by (unfold E; rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 (wf_p F))
  by (unfold E; rewrite (ew_Ereg_nat (ms_regs ms) _ 19 19%bv eq_refl); exact R19).
assert (E23 : ew E 23 = Z_to_bv 64 (wf_d F))
  by (unfold E; rewrite (ew_Ereg_nat (ms_regs ms) _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Hlo : alloc_ceiling <= wf_sp F - WVC_F) by lia.
(* the run to indent *)
eapply (wvc_seg_open_ind B W ms mdc E (wf_ty F) (wf_n F) (wf_d F) (wf_p F) (wvc_STK F) (wf_ot F) (wf_sp F) (wvc_FP F)
  ly0 S0 W0 (unpoison U0 mem0) md0 [] ly S U (wevk (wf_cap0 F) st) Q).
{ split; [exact HS0|]. split; [exact SHOK|]. split; [exact HJ | exact HARU]. }
{ destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty. }
{ rewrite EX. reflexivity. }
{ exact Hn0. }
{ lia. }
{ exact E23. }
{ rewrite EX. reflexivity. }
{ lia. }
{ exact E19. }
{ exact HE_p. }
{ exact E2. }
{ lia. }
{ unfold wvc_STK. lia. }
intros ms' mdc' HJ1 HARU1 HFR HCSL R1 R10 R11 R12 R2 RK R18 R20 R21 R22 R23' R24 R25 R26 Ems'.
rewrite Ems'.
set (regsC := ms_regs ms') in *. set (memC := ms_mem ms') in *.
pose proof (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) memC mdc' buf st HSEM HARU1 HFR Hlo
  ltac:(lia) ltac:(lia)) as HSEMC.
assert (EspC : spZ regsC = wf_sp F - WVC_F) by (unfold spZ at 1; rewrite R2; exact Hsp).
pose proof HJ1 as (_ & Hly & _ & _ & _ & Hfrs & Hnev & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
(* indent's frame-chain, presence and fpreU at the call *)
pose proof HCSL as HCSL0. unfold wvc_csL in HCSL0. apply Forall_app in HCSL0 as (_ & HCS0).
assert (HC1 : wf_o F = wf_sp F + 8 ->
  rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8) = Some (raZ regs0)).
{ intros _. exact (wvc_ra_slot B ly S U W memC mdc' (ms_regs ms) regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F)
    (wf_d F) (wf_keys F) 0 (wf_sp F) HARU1 HCS0 Hlo ltac:(lia)). }
destruct (wvc_callpre B F ly0 S0 U0 W0 mem0 md0 regs0 ly S U W memC mdc' (wevk (wf_cap0 F) st) buf st regsC STK_indent
  HJ1 HARU1 HSEMC HC1 EspC HE_sp16 HE_ot16 ltac:(lia) SKi0 HSind
  ltac:(rewrite R1; unfold w64; apply wvc_ret_ok_lit; [unfold WVC_R_IND; lia | reflexivity])
  ltac:(unfold raZ; rewrite R1; unfold w64; rewrite wz by (unfold WVC_R_IND; lia); unfold WVC_R_IND; lia)
  ltac:(rewrite (RK 3%bv ltac:(wvc_inl)), R3; exact HE_gp) ltac:(rewrite (RK 4%bv ltac:(wvc_inl)), R4; exact HE_tp)
  ltac:(unfold s0Z; rewrite (RK 8%bv ltac:(wvc_inl)), R8; unfold w64; apply wz; lia)
  HE_oot ltac:(rewrite Etop; exact HE_top) HE_o8 Hlo)
  as (ch & _ & HPREC & HCHC & HPRC).
(* the writer facts at the call *)
pose proof HSEMC as (HOUTC & (peak & Hpk & HGLC) & HHDC & _ & _ & HBKC & HCNTC & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & HU0C).
pose proof HOUTC as (_ & _ & _ & _ & _ & Hcap64 & _).
pose proof HBKC as (HCAPC & Hbb & _).
assert (HBUDI : wbudget_pre S (WriterApp.w_cap st) (WriterApp.w_cnt st) (wf_live F - wf_cap0 F + WriterApp.w_cap st)
  (WriterApp.putN (WriterApp.mkW (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st)
    (WriterApp.w_cnt st) (WriterApp.w_fail st) []) Pc)).
{ pose proof HE_bud as HB. rewrite HWP in HB.
  pose proof (wv_budget_pre_mid S0 S (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
    Pd (Pc ++ Rest) HE_cap0 HB Hnev Hbb HCNTC) as HB2.
  exact (wv_budget_pre_prefix S (WriterApp.w_cap st) (WriterApp.w_cnt st) (wf_live F - wf_cap0 F + WriterApp.w_cap st)
    (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_fail st) Pc Rest ltac:(lia) HB2). }
assert (HROOMI : Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat Pc)) + 1 <= WMAX).
{ pose proof HE_room as HR. rewrite HWP in HR.
  pose proof (wv_room_mid (wvc_st0 F) Pd (Pc ++ Rest)) as Hrm.
  change (WriterApp.w_text (wvc_st0 F)) with (wf_text0 F) in Hrm.
  assert (Hcc : (length (concat Pc) <= length (concat (Pc ++ Rest)))%nat) by (rewrite concat_app, length_app; lia).
  unfold st, wvc_stP. lia. }
(* indent (pretty, d + 1) *)
eapply SRr_bind.
{ apply (HIND ly S U W regsC memC mdc' ch (wf_ot F) (wf_o F) (wf_p F) (wf_d F + 1) buf (WriterApp.w_cap st)
    (WriterApp.w_failed st) (WriterApp.w_text st) (wf_live F - wf_cap0 F + WriterApp.w_cap st) peak
    (WriterApp.w_cnt st) (WriterApp.w_fail st) HPREC HHDC).
  - rewrite Hfrs. cbn [app]. exact HE_frl.
  - rewrite R10, E8. reflexivity.
  - rewrite R11, E19. reflexivity.
  - exact R12.
  - exact HE_p.
  - lia.
  - exact HOUTC.
  - replace (wf_live F - wf_cap0 F + WriterApp.w_cap st) with (wf_live F + WriterApp.w_cap st - wf_cap0 F) by lia.
    exact HGLC.
  - exact HU0C.
  - lia.
  - exact HE_oot.
  - exact HE_ot16.
  - rewrite Etop. exact HE_top.
  - exact HCHC.
  - exact HPRC.
  - exact HROOMI.
  - exact HCAPC.
  - lia.
  - exact HBUDI. }
intros W' c' _ (st' & buf' & U' & Est & HUS' & Hwp).
unfold wpost, fpostU in Hwp.
destruct Hwp as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & HOUT' & HBK' & HBS' & HWK' & HGL').
rewrite R1.
assert (Ecal : WriterApp.putN (wv_rst st) Pc = st') by (rewrite Est; reflexivity).
destruct (wvc_ret_inv B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_oot HE_top HE_top47 HE_lo HE_cap0 HE_cnt0 HE_p
  HE_d HE_dd HE_bud HE_ty HE_hdr HE_n HE_kk WVC_R_IND 0 Pd Pc Rest ly S U W memC mdc' buf regsC (ms_regs ms)
  (wf_keys F) 0 STK_indent peak ly' S' U' W' regs' mem' md' buf' HWP HJ1 HARU1 HSEMC Hpk HCSL R9 EspC
  ltac:(rewrite (RK 8%bv ltac:(wvc_inl)); exact R8) ltac:(rewrite (RK 9%bv ltac:(wvc_inl)); exact R9)
  ltac:(rewrite (RK 19%bv ltac:(wvc_inl)); exact R19) R21 R25 R22
  ltac:(rewrite (RK 3%bv ltac:(wvc_inl)); exact R3) ltac:(rewrite (RK 4%bv ltac:(wvc_inl)); exact R4)
  ltac:(rewrite R18; exact (wvc_den_val E (wvc_shv 9 40) _ (wvc_shv_U E 40 (wf_v F) E9 E32 ltac:(lia) ltac:(lia)
    ltac:(lia))))
  ltac:(rewrite R20; exact (wvc_den_val E (SOff 9 40) _ (wvc_u_off E 9 (wf_v F) 40 E9 ltac:(lia) ltac:(lia))))
  ltac:(rewrite R23'; exact (wvc_den_val E (SOff 9 24) _ (wvc_u_off E 9 (wf_v F) 24 E9 ltac:(lia) ltac:(lia))))
  R24
  ltac:(rewrite R26; exact (wvc_den_val E (wvc_shv 9 24) _ (wvc_shv_U E 24 (wf_v F) E9 E32 ltac:(lia) ltac:(lia)
    ltac:(lia))))
  ltac:(rewrite (RK 27%bv ltac:(wvc_inl)); exact R27)
  ltac:(lia)
  ltac:(try change (wvc_stP F Pd) with st; rewrite Ecal; exact HJc) OK' PO' HP SKi0 HSind HUS'
  ltac:(try change (wvc_stP F Pd) with st; rewrite Ecal; exact HOUT')
  ltac:(try change (wvc_stP F Pd) with st; rewrite Ecal; exact HBK')
  ltac:(try change (wvc_stP F Pd) with st; rewrite Ecal; exact HBS') HWK'
  ltac:(try change (wvc_stP F Pd) with st; rewrite Ecal; destruct HGL' as (pk & Hpk' & HG); exists pk; split; [lia|];
        replace (wf_live F + WriterApp.w_cap st - wf_cap0 F + WriterApp.w_cap st' - WriterApp.w_cap st)
          with (wf_live F - wf_cap0 F + WriterApp.w_cap st + WriterApp.w_cap st' - WriterApp.w_cap st) by lia;
        exact HG))
  as (key' & HINV).
replace (wf_keys F + 8 * 0) with (wf_keys F) in HINV by lia.
exact (K ly' S' U' W' regs' mem' md' buf' key' HINV).
Qed.

End A.
