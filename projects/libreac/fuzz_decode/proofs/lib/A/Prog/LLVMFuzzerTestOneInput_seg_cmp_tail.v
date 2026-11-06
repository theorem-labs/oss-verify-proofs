(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_seg_cmp_tail: proves no function (kind: segment lemma).
   cmp_tail, the last piece of the cmp segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput
   (lib/A/Prog/LLVMFuzzerTestOneInput_seg_cmp.v): from the cut point cmp_q734 (+0x734) the machine SRr-realizes
   llvm_a_st_748 (the return of reac_upstream_channels).

   The code (offsets from DEC_A_LLVMF, map-code.md section 2, DecodeList.v:489-493):
     +0x734  mv a0,a7                                   a0 := out, the decode buffer
     +0x738  jal ra,__interceptor_trampoline_free       free #1 (returns to +0x73c)
     +0x73c  ld s10,56(s1)                              s10 := len (spill slot 56)
     +0x740  mv a0,s10
     +0x744  jal ra,reac_upstream_channels              (returns to +0x748, the post)

   Shape of the proof, following LLVMFuzzerTestOneInput_seg_entry.v (a Theorem Labs lane's Qed walk of this engine) and the
   exit lane's free piece (LLVMFuzzerTestOneInput_seg_exit_free.v, a Theorem Labs lane): two short runs, each seated FRESH on the
   concrete state the previous step left; free #1 by lib/A/Prog/YC85.v afree04_sub at the premise afree04_rule;
   reac_upstream_channels by its leaf statement through the shared bridge LLVMFuzzerTestOneInput_leafb.v
   (dec_leafb_journal, dec_leafb_rng, dec_leafb_covers_visible, dec_leafb_mrd_aview), its ÷36 word from the owned
   constant cell of dec_crt_cells; then the post, dec_a_mode_ok carried by cmp_mode_re through the read-only view
   at the DEC_RO_RD bytes.
   The helpers of section 1 are copied from the sibling lanes (named at each one). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0p.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YI00 YO09 YM05 YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaRun PaShadow PaJournal PaStep DecodeSyms DecodeList DecodeAddr DecodePa DecodeImg DecodePaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC1g YC1h YC1i YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require
reac_upstream_channels_cg reac_decode_plain_le_c reac_upstream_channels_c reac_frame_inspect_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_leafb.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_seg_cmp_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module CPlain := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_plain_le_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_c.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_c.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_cg.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it (the sibling lanes'
   line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. Helpers                                                           *)
(* ------------------------------------------------------------------ *)

(* LLVMFuzzerTestOneInput_seg_exit_free.v xf_flat / xf_trace: call_trace0 of YCbq is check_round_trip_cg's dec_utrace
   at the chain's return addresses. *)
Lemma ct_flat : forall pc0 ch,
  flat_map (fun r : Z * Z * Z => match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end) ch =
  flat_map (fun ra : Z => if ra =? pc0 then [] else [ra]) (spine ch).
Proof.
intros pc0 ch. induction ch as [|[[fp ra] v] ch IH]; cbn [flat_map spine map]; [reflexivity|].
rewrite IH. reflexivity.
Qed.
Lemma ct_trace : forall pc0 regs ch, call_trace0 pc0 regs ch = dec_utrace pc0 (raZ regs :: spine ch).
Proof.
intros pc0 regs ch. unfold call_trace0, unwind_of_chain, dec_utrace.
cbn [flat_map]. rewrite ct_flat. reflexivity.
Qed.

(* LLVMFuzzerTestOneInput_seg_exit_free.v xf_pw_nodup: the blocks of one state are pairwise disjoint, so no block is
   listed twice. *)
Lemma ct_pw_nodup : forall l : list (Z * Z), Forall (fun b : Z * Z => 0 <= snd b) l ->
  pairwise zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
intros l. induction l as [|x l IH]; intros HF HP; [apply List.NoDup_nil|].
cbn [map] in HP. destruct HP as [HFa HP]. inversion HF as [|x0 l0 Hx HFl]; subst.
apply List.NoDup_cons; [|exact (IH HFl HP)].
intros Hin.
pose proof (proj1 (Forall_forall _ _) HFa (fst x, req_size (snd x))
  (in_map (fun b : Z * Z => (fst b, req_size (snd b))) l x Hin)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos (snd x) Hx) as [H1 _]. lia.
Qed.

(* LLVMFuzzerTestOneInput_seg_crt1.v c1_saved_at_range. *)
Lemma ct_saved_at_range : Forall (fun o : Z * Z => 8 <= fst o <= 104) dec_a_saved_at.
Proof. unfold dec_a_saved_at. repeat constructor; cbn [fst]; lia. Qed.

Section cmpt.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.
Local Abbreviation SEGS := (@pa_segs _ decode_listing PI_decode).
Local Abbreviation VAL := (@pa_val _ decode_listing PI_decode).
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).

(* LLVMFuzzerTestOneInput_seg_crt1.v c1_rdword_kept / c1_garr8_kept, between two worlds. *)
Lemma ct_rdword_kept : forall (W W' : world segs) mem mem' a v,
  (forall k, 0 <= k < 8 -> aview segs (w_H W') mem' (a + k) = aview segs (w_H W) mem (a + k)) ->
  rdword (aview segs (w_H W) mem) a = Some v -> rdword (aview segs (w_H W') mem') a = Some v.
Proof. intros W W' mem mem' a v Hk H. rewrite (rdword_ext _ _ a Hk). exact H. Qed.

Lemma ct_garr8_kept : forall (W W' : world segs) mem mem' p (l : list Z),
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs (w_H W') mem' (p + k) = aview segs (w_H W) mem (p + k)) ->
  garr8 segs (mrestrict (w_H W) mem) p l -> garr8 segs (mrestrict (w_H W') mem') p l.
Proof.
intros W W' mem mem' p l Hk H j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk1. rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (p + Z.of_nat j + Z.of_nat k)).
- exact (Hv k Hk1).
- replace (p + Z.of_nat j + Z.of_nat k) with (p + (Z.of_nat j + Z.of_nat k)) by lia. apply Hk. lia.
Qed.

(* dec_a_saved is read only in the 104 bytes below the entry sp. *)
Lemma ct_saved_kept : forall cx (r r' : reader),
  (forall a, d_sp0 cx - 104 <= a < d_sp0 cx -> r' a = r a) -> dec_a_saved cx r -> dec_a_saved cx r'.
Proof.
intros cx r r' HK Hsv. unfold dec_a_saved in *. rewrite Forall_forall in Hsv |- *. intros o Ho.
pose proof (proj1 (Forall_forall _ _) ct_saved_at_range o Ho) as Ro. cbv beta in Ro.
rewrite (rdword_ext r r' _); [exact (Hsv o Ho)|]. intros k Hk. apply HK. lia.
Qed.

(* The env of a seat: the registers as atoms 0..31, then the extra atoms (LLVMFuzzerTestOneInput_seg_exit_free.v
   xf_E and its three facts). *)
Definition ct_E (regs : bvmap 5 word) (extra : list word) : env := @Eimg rc decode_listing PI_decode (Ereg regs extra).
Lemma ct_E_img : forall regs extra, img_env VAL A_LIM (ct_E regs extra).
Proof. intros regs extra. unfold ct_E. apply Eimg_env. Qed.
Lemma ct_E_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ct_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold ct_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ct_E_agree : forall regs extra, env_agree 32 (Ereg regs extra) (ct_E regs extra).
Proof.
intros regs extra. split; [|reflexivity].
intros n Hn. unfold ct_E. first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia.
Qed.
Lemma ct_E_33 : forall regs v0 v1, ew (ct_E regs [v0; v1]) 33 = v1.
Proof. intros regs v0 v1. unfold ct_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1%nat). Qed.

(* The seat at +0x734: no region (the run moves a register and calls). *)
Definition ct_ss1 : sstate := mkSS 0x734 sr_atoms [] None (mkFacts [] [] []).
Lemma ct_seat1 : forall (fxx : YK11.FPState) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte),
  st_ok_pi SEGS VAL (ct_E regs []) ct_ss1
    (restrict (w_H W) (@YK11.mkst fxx regs (Z_to_bv 64 (BASE + 0x734)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxx W regs mem. rewrite restrict_mkst_fx. unfold ct_ss1.
apply pa_entry_st_ok_full.
- unfold ct_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto.
Qed.

(* The seat at +0x73c: the spill slot 56(s1) as a read-only region over s1 (atom 9), holding atom 33 = len. *)
Definition ct_r56 : YP09.region := YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 33 0))].
Definition ct_ss2 : sstate := mkSS 0x73c sr_atoms [ct_r56] None (mkFacts [] [] []).
Lemma ct_seat2 : forall (fxx : YK11.FPState) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (sp1 len : Z),
  YK11.getr regs 9 = w64 sp1 -> 0 <= sp1 -> sp1 + 64 < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some len ->
  st_ok_pi SEGS VAL (ct_E regs [w64 SHADOW_OFF; w64 len]) ct_ss2
    (restrict (w_H W) (@YK11.mkst fxx regs (Z_to_bv 64 (BASE + 0x73c)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxx W regs mem sp1 len R9 H0 H1 Hrd. rewrite restrict_mkst_fx. unfold ct_ss2.
apply pa_entry_st_ok_full.
- unfold ct_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, ct_r56. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (ct_E_reg regs _ 9 9%bv eq_refl), R9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  exact (cmp_chunk _ W mem 33%nat sp1 56 len (ct_E_33 regs (w64 SHADOW_OFF) (w64 len)) Hrd).
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto.
Qed.

(* The registers a run leaves as they were. *)
Definition ct_keep1 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ct_keep2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv.

(* The value of register r in the machine state of a symbolic state HS (LLVMFuzzerTestOneInput_seg_entry.v
   reg_at). *)
Ltac ct_reg_at HS r v H tac :=
  lazymatch type of HS with st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac ct_in := unfold ct_keep1, ct_keep2; cbn [List.In]; repeat (first [left; reflexivity | right]).
Ltac ct_inz := cbn [List.In]; repeat (first [left; reflexivity | right]).
(* membership of Z_to_bv 5 r in a list of register literals: the literals and Z_to_bv agree on bv_unsigned *)
Ltac ct_inb := unfold ct_keep1, ct_keep2; cbn [List.In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Ltac ct_mdv :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    lazymatch mdx with
    | with_vm_backing _ _ _ => let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv
    | _ => idtac end end.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section body.
Context {fx : YK11.FPState}.

Lemma ct_body : forall (cx : dctx) (W : world decodesegs0) regs mem md,
  @cmp_prem rc RA_LLVMF B MT ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_a_rom cx ->
  @cmp_q734 rc B MT cx W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x734)) mem (YK11.seg_rom decodesegs0)) md) ->
  SRr decodesegs0 W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x734)) mem (YK11.seg_rom decodesegs0)) md)
    (@llvm_a_st_748 rc B MT cx).
Proof.
intros cx W regs mem md HPREM HB HR H734.
destruct HPREM as (HPCF & HUTR & HCELLS & HROS & HRONE & LAWS & ML & MTL & ABCMP & AFREE & LUC).
destruct H734 as (fx5 & ly1 & S1 & regs1 & mem1 & md1 & res & out & mode & nch & ns &
  Hc5 & Hfrm5 & Hcore & Hperm & Hres4096 & Hout4096 & Hmle & Hmok & Hfr & Ra7 & Rs2 & Rs4 &
  Hmode & Hfsh & Hgarr & Hguard & Hsl40 & Hsl56 & Hsl64 & Hsl72 & Hsl112).
injection Hc5 as Hregs Hfpr Hfcs Hmem Hmd.
subst regs1 mem1 md1.
assert (Hfrm : frm_zero (@fp_csr fx)) by (first [rewrite Hfcs | rewrite <- Hfcs]; exact Hfrm5).
clear Hfrm5 Hfpr Hfcs. clear fx5.
unfold dec_a_slot in Hsl40, Hsl56, Hsl64, Hsl72, Hsl112.
(* ---- the entry ---- *)
pose proof HB as HB0. unfold dec_a_base, dec_lib_pre_x in HB.
destruct HB as (HAFN & HraE & _ & _ & Hpn & Hplen & _ & _ & Hnev0 & _).
pose proof HAFN as (HAR0 & Hraok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
change (spZ (d_regs cx)) with (d_sp0 cx) in Hstk0, Hpres0, Hch0.
pose proof Hstk0 as (Hsp16 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H47 & Hbot0 & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : DEC_LLVMF_STK = 32768) by reflexivity.
assert (HASv : ASTACK = 16384) by reflexivity.
assert (HESv : ESTACK = 4096) by reflexivity.
assert (HSP0c : alloc_ceiling + 32768 <= d_sp0 cx) by lia.
(* ---- the cut state ---- *)
destruct Hcore as (HJ & Hfrs & R8 & R9 & Hsp & Hsp240 & Hsp32 & Rgp & Rtp & Hsaved & HF4096 & HF32 & HFpres & HFL
  & Hblk & Hgarrp).
pose proof Hfr as (Rs3 & Rs5 & Rs11).
pose proof HJ as (HAR1 & Hly1 & _ & _ & _ & _ & Hnev1 & _).
assert (HSP116 : d_sp1 cx mod 16 = 0) by lia.
assert (HSP08 : d_sp0 cx mod 8 = 0) by lia.
assert (HSP1c : alloc_ceiling <= d_sp1 cx) by lia.
assert (HSP0u : 0 <= d_sp0 cx <= 2 ^ 47) by lia.
assert (HTOP64 : ly_top (d_ly cx) <= 2 ^ 64) by lia.
assert (Hlen : 0 <= dec_a_len (d_n cx) < 2 ^ 26) by (unfold dec_a_len; destruct Hpn as [[Hn0 _] | [Hn0 _]]; lia).
assert (Hblen : Z.of_nat (length (d_body cx)) = dec_a_len (d_n cx)).
{ unfold d_body, dec_a_u, dec_a_len. rewrite length_skipn. lia. }
assert (Hfa : forall cid pos, frame_addr ly1 cid pos = frame_addr (d_ly cx) cid pos).
{ destruct Hly1 as (_ & _ & _ & _ & _ & EF & _). intros cid pos. unfold frame_addr. rewrite EF. reflexivity. }
(* ---- the blocks of the cut state are distinct: out is not an entry block, nor res ---- *)
assert (HND : List.NoDup (ablocks B ly1 S1)).
{ apply ct_pw_nodup.
  - apply Forall_forall. intros [b m] Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia.
  - destruct (al_sep _ _ LAWS _ _ _ _ _ HAR1) as (Hpw & _).
    exact (proj1 (pairwise_app_l _ _ _ Hpw)). }
pose proof (Permutation_NoDup Hperm HND) as HND2.
rewrite app_assoc in HND2.
pose proof (NoDup_remove_2 _ _ _ HND2) as HX.
assert (HnotO : ~ List.In (out, dec_a_olen nch ns) (ablocks B (d_ly cx) (d_S cx))).
{ intros Hin. apply HX. apply in_or_app. left. apply in_or_app. left. exact Hin. }
assert (HRO : (res, dec_a_len (d_n cx)) <> (out, dec_a_olen nch ns)).
{ intros Heq. apply HX. apply in_or_app. left. apply in_or_app. right. left. exact Heq. }
clear HX HND2.
assert (HinO : List.In (out, dec_a_olen nch ns) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; right. left. reflexivity. }
assert (HinR : List.In (res, dec_a_len (d_n cx)) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; left. left. reflexivity. }
(* ---- the chain and the trace of the free call (LLVMFuzzerTestOneInput_seg_exit_free.v CHAIN / HTRACE) ---- *)
assert (CHAIN : forall (Wc : world segs) (memc : word -> option byte) lyc Sc mdc kk (regsT : bvmap 5 word),
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] lyc Sc Wc memc mdc kk ->
  dec_a_saved cx (aview segs (w_H Wc) memc) ->
  YK11.getr regsT 8 = w64 (d_sp0 cx) -> spZ regsT = d_sp1 cx -> 4096 <= raZ regsT ->
  exists ch, chain_pre lyc (aview segs (w_H Wc) memc) regsT ch /\ List.In (spine ch) [[]; [RA_LLVMF]]).
{ intros Wc memc lyc Sc mdc kk regsT HJx HSVx Rs0 Rsp Rra.
  pose proof HJx as (HARx & Hlyx & _ & _ & _ & _ & _ & _ & F1x & _).
  assert (Etop : ly_top lyc = ly_top (d_ly cx))
    by (destruct Hlyx as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
  assert (Hs0v : s0Z regsT = d_sp0 cx)
    by (unfold s0Z; rewrite Rs0; unfold w64; apply unsigned_lit_small; lia).
  unfold dec_a_saved, dec_a_saved_at in HSVx.
  pose proof (proj1 (Forall_forall _ _) HSVx (8, 1) ltac:(cbn [In]; left; reflexivity)) as Hw8.
  pose proof (proj1 (Forall_forall _ _) HSVx (16, 8) ltac:(cbn [In]; right; left; reflexivity)) as Hw16.
  cbn [fst snd] in Hw8, Hw16.
  destruct (Z_lt_le_dec (d_sp0 cx) (ly_top (d_ly cx) - 16)) as [Hlt | Hge].
  - exists [(d_sp0 cx, raZ (d_regs cx), s0Z (d_regs cx))].
    split; [| rewrite HraE; cbn [spine map fst snd]; right; left; reflexivity].
    eapply (achain_chain_pre lyc (aview segs (w_H Wc) memc) (d_sp1 cx) (d_sp0 cx) _ regsT);
      [| lia | exact Hs0v | exact Rra].
    apply (achain_ly_top (d_ly cx) lyc _ _ _ _ Etop).
    eapply (achain_push (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx)) (aview segs (w_H Wc) memc)
      (d_sp0 cx) (s0Z (d_regs cx)) (raZ (d_regs cx)) [] (d_sp1 cx) Hch0 HTOP64);
      [ intros a Ha; apply F1x; lia | exact Hw8 | exact Hw16 | exact Hra40 | lia | exact HSP08 | lia | lia ].
  - exists []. split; [| left; reflexivity].
    eapply (achain_chain_pre lyc (aview segs (w_H Wc) memc) (d_sp1 cx) (d_sp0 cx) [] regsT);
      [| lia | exact Hs0v | exact Rra].
    left. split; [right; left; lia | reflexivity]. }
assert (HTRACE : forall (regsT : bvmap 5 word) ch, List.In (spine ch) [[]; [RA_LLVMF]] ->
  List.In (raZ regsT) DEC_LLVMF_RA_FREE ->
  List.In (call_trace0 (pc_free_ra0 (as_code B)) regsT ch) (as_universe B)).
{ intros regsT ch Hsp' Hra'. rewrite ct_trace. destruct (HUTR (spine ch) Hsp') as (_ & Hfree). apply Hfree. exact Hra'. }
(* ---- what the free keeps (LLVMFuzzerTestOneInput_seg_exit_free.v KEEP) ---- *)
assert (KEEP : forall (Wb Wa : world segs) (mb ma : word -> option byte) lyb Sb mdb (pa nn : Z),
  AR segs B lyb Sb Wb mb mdb ->
  List.In (pa, nn) (ablocks B lyb Sb) ->
  frames Sb = [(DEC_FCLASS, d_fpos cx)] ->
  (forall cid pos, frame_addr lyb cid pos = frame_addr (d_ly cx) cid pos) ->
  acall_kept segs B lyb Sb Wb mb Wa ma (d_sp1 cx - ASTACK) (d_sp1 cx) (fun a => pa <= a < pa + req_size nn) ->
  (forall a, d_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H Wa) ma a = aview segs (w_H Wb) mb a) /\
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H Wa) ma a = aview segs (w_H Wb) mb a) /\
  (forall i, 0 <= i < 8 -> aview segs (w_H Wa) ma (d_SH cx + i) = aview segs (w_H Wb) mb (d_SH cx + i)) /\
  (forall b m i, List.In (b, m) (ablocks B lyb Sb) -> (b, m) <> (pa, nn) -> 0 <= i < req_size m ->
     aview segs (w_H Wa) ma (b + i) = aview segs (w_H Wb) mb (b + i))).
{ intros Wb Wa mb ma lyb Sb mdb pa nn HARb Hinb Hfrsb Hfab HK.
  pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (Hfin : List.In (DEC_FCLASS, d_fpos cx) (frames Sb)) by (rewrite Hfrsb; left; reflexivity).
  assert (HF2 : frame_addr lyb DEC_FCLASS (d_fpos cx) = d_F cx) by (rewrite Hfab; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ pa nn HARb Hinb) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbn).
  pose proof (req_size_pos nn ltac:(lia)) as (Hrq1 & Hrq2).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ DEC_FCLASS (d_fpos cx) HARb Hfin) as (HFb4096 & HFbceil & _).
  pose proof (sep_block_frame segs B LAWS _ _ _ _ _ pa nn DEC_FCLASS (d_fpos cx) HARb Hinb Hfin) as Hdf.
  unfold zdisjoint, frame_rng in Hdf. cbn [fst snd] in Hdf. rewrite HF2 in Hdf.
  change (fs_frame_bytes DEC_FCLASS) with 64 in Hdf, HFbceil.
  rewrite HF2 in HFbceil.
  unfold in_app in Hbapp.
  assert (HLSB : kLowShadowBeg < SHADOW_OFF) by (unfold kLowShadowBeg, SHADOW_OFF; lia).
  assert (HSHlo : SHADOW_OFF <= shadow_addr (d_F cx)) by (unfold shadow_addr; lia).
  assert (HSHhi : shadow_addr (d_F cx) + 8 <= kHighMemBeg)
    by (unfold shadow_addr, SHADOW_OFF; rewrite C3; unfold ASAN_CEIL in *; lia).
  split; [|split; [|split]].
  - intros a Ha. apply K1; lia.
  - intros a Ha. apply (K4 DEC_FCLASS (d_fpos cx) a Hfin).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HF2. change (fs_frame_bytes DEC_FCLASS) with 64. lia.
    + cbn beta. lia.
  - intros i Hi. unfold d_SH. apply (K4 DEC_FCLASS (d_fpos cx) (shadow_addr (d_F cx) + i) Hfin).
    + right. unfold in_zr. cbn [fst snd]. rewrite HF2. change (fs_frame_bytes DEC_FCLASS / 8) with 8. lia.
    + cbn beta. lia.
  - intros b m i Hin2 Hne Hi. apply (K2 b m i Hin2 Hi).
    pose proof (sep_blocks segs B LAWS _ _ _ _ _ b m pa nn HARb Hin2 Hinb Hne) as Hd2.
    unfold zdisjoint in Hd2. cbn [fst snd] in Hd2. cbn beta. lia. }
(* ---- +0x734 .. +0x738: mv a0,a7 and the jal into the free wrapper ---- *)
assert (HBASEeq : DEC_A_LLVMF = BASE) by (vm_compute; reflexivity).
assert (HBASEb : 4096 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64)
  by (split; [vm_compute; discriminate | vm_compute; reflexivity]).
assert (Hpcw : forall o : Z, w64 (DEC_A_LLVMF + o) = Z_to_bv 64 (BASE + o))
  by (intros o; unfold w64; rewrite HBASEeq; reflexivity).
rewrite (Hpcw 0x734).
pose proof (@paj_run fx rc dec_A_sink_head decode_listing PL_decode PI_decode B LAWS) as RUN.
pose proof (ct_E_img regs []) as HEIa.
pose proof (ct_seat1 fx W regs mem) as HSa.
assert (SHOKa : sh_ok SEGS (SOff 32 0) (@nil shent) (ct_E regs []) (mrestrict (w_H W) mem)) by constructor.
pose proof HJ as HJa.
paj_run_tok RUN HSa HJa SHOKa Bspan; [apply awr_ok_nil |].
rename ms into msA.
ct_mdv.
assert (HM1 : forall a, ms_mem msA a = mem a).
{ intros x. apply HF. intros (r & Hin & _). unfold ct_ss1 in Hin. cbn [ss_mem In] in Hin. exact Hin. }
clear HF HFr HG.
assert (HV1 : forall a, aview segs (w_H W) (ms_mem msA) a = aview segs (w_H W) mem a).
{ intros a. apply aview_eq_of. unfold mrestrict. rewrite HM1. reflexivity. }
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs [] ct_keep1 HSa (ct_E_agree regs []) ltac:(vm_compute; reflexivity))
  as QK1.
cbn [ms_regs restrict] in QK1.
ct_reg_at HSa (10%bv : bv 5) (w64 out) Q10
  ltac:(cbn [sv_denot]; rewrite (ct_E_reg regs [] 17 17%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ra7).
ct_reg_at HSa (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x73c)) Q1 ltac:(apply codeptr_val; exact HEIa).
assert (Qsp : spZ (ms_regs msA) = d_sp0 cx + (d_sp1 cx - d_sp0 cx)).
{ unfold spZ. rewrite (QK1 2%bv ltac:(ct_in)). unfold spZ in Hsp. lia. }
assert (Q3 : YK11.getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite (QK1 3%bv ltac:(ct_in)); exact Rgp).
assert (Q4 : YK11.getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite (QK1 4%bv ltac:(ct_in)); exact Rtp).
assert (Q8 : YK11.getr (ms_regs msA) 8 = w64 (d_sp0 cx)) by (rewrite (QK1 8%bv ltac:(ct_in)); exact R8).
assert (Qraz : raZ (ms_regs msA) = BASE + 0x73c) by (unfold raZ; rewrite Q1; apply unsigned_lit_small; lia).
assert (HSVa : dec_a_saved cx (aview segs (w_H W) (ms_mem msA)))
  by exact (ct_saved_kept cx _ _ (fun a _ => HV1 a) Hsaved).
destruct (CHAIN W (ms_mem msA) ly1 S1 _ dec_ev_5fc (ms_regs msA) HJa HSVa Q8 ltac:(rewrite Qsp; lia)
  ltac:(rewrite Qraz; lia)) as (ch & Hchp & Hspn).
assert (Htrc : List.In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs msA) ch) (as_universe B)).
{ apply HTRACE; [exact Hspn|]. rewrite Qraz. unfold DEC_LLVMF_RA_FREE. cbn [map List.In]. left.
  rewrite HBASEeq. reflexivity. }
assert (Ho16 : (d_sp1 cx - d_sp0 cx) mod 16 = 0) by lia.
assert (Hnevf : st_nev S1 < EV_MAX) by (unfold dec_ev_5fc, DEC_EV_LIB in *; lia).
assert (Hmof : mo_ok MT S1 (mo_free MT)).
{ apply (mo_ok_le MT MTL S1 (mo_free MT) (dec_rest_5fc MT) Hmok).
  unfold dec_rest_5fc, dec_rest_748, dec_rest_86c, dec_crt_cost_max.
  pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
pmkst HSa.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (YK11.mkst rg (Z_to_bv 64 (decode_sigma DS___interceptor_trampoline_free)) mm rom) mdx) Q) end.
rewrite <- HPCF.
(* state the call over decodesegs0, so that the worlds after it are worlds of decodesegs0 *)
change SEGS with segs.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
  exact (@afree04_sub fx rc dec_A_sink_head segs B LAWS decode_segs_low MT (AFREE fx) W (ms_regs msA) (ms_mem msA)
    DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)]
    ly1 S1 mdx dec_ev_5fc out (dec_a_olen nch ns) (d_sp1 cx - d_sp0 cx) (Z_to_bv 64 (BASE + 0x73c)) ch
    HJa HinO Q10 Qsp Ho16 ltac:(lia) ltac:(lia) Q3 Q4 Q1 (ret_ok_codeptr_v (PI := PI_decode) 0x73c ltac:(lia) eq_refl)
    Hnevf Hchp Htrc (fun Hin => False_ind _ (HnotO Hin)) Hmof) end. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Hbl1 & Hbl2) & Hfr2 & HK2
  & MLE2 & _).
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx)) with (d_sp1 cx) in HK2 by lia.
destruct (KEEP W W2 (ms_mem msA) mem2 ly1 S1 _ out (dec_a_olen nch ns) (proj1 HJa) HinO Hfrs Hfa HK2)
  as (K1 & K2 & K3 & K4).
(* ---- +0x73c .. +0x744: ld s10,56(s1), mv a0,s10 and the jal into reac_upstream_channels ---- *)
assert (Q9b : YK11.getr regs2 9 = w64 (d_sp1 cx)).
{ transitivity (YK11.getr (ms_regs msA) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia))|].
  rewrite (QK1 9%bv ltac:(ct_in)). exact R9. }
assert (Hrd56 : rdword (aview segs (w_H W2) mem2) (d_sp1 cx + 56) = Some (dec_a_len (d_n cx))).
{ apply (ct_rdword_kept W W2 mem mem2); [|exact Hsl56]. intros k Hk. rewrite (K1 (d_sp1 cx + 56 + k)) by lia.
  apply HV1. }
pose proof (ct_seat2 fx W2 regs2 mem2 (d_sp1 cx) (dec_a_len (d_n cx)) Q9b ltac:(lia) ltac:(lia) Hrd56) as HSb.
pose proof (ct_E_img regs2 [w64 SHADOW_OFF; w64 (dec_a_len (d_n cx))]) as HEIb.
assert (SHOKb : sh_ok SEGS (SOff 32 0) (@nil shent) (ct_E regs2 [w64 SHADOW_OFF; w64 (dec_a_len (d_n cx))])
  (mrestrict (w_H W2) mem2)) by constructor.
pose proof HJ2 as HJb.
clear HSa SHOKa.
paj_run_tok RUN HSb HJb SHOKb Bspan;
  [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
rename ms into msB.
ct_mdv.
(* the run's journal, restated over decodesegs0 (the run lemma states it over pa_segs) *)
lazymatch type of HJb with @ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx ?kx =>
  assert (HJbd : @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx)
    (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 (ms_mem msB) mdx kx) by exact HJb end.
clear HJb.
assert (HM2 : forall a, ms_mem msB a = mem2 a).
{ intros x. apply HF. intros (r & Hin & Ha). unfold ct_ss2 in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | []]. unfold ct_r56 in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
clear HF HFr HG.
assert (HV2 : forall a, aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mem2 a).
{ intros a. apply aview_eq_of. unfold mrestrict. rewrite HM2. reflexivity. }
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 _ ct_keep2 HSb (ct_E_agree regs2 _) ltac:(vm_compute; reflexivity))
  as PK.
cbn [ms_regs restrict] in PK.
ct_reg_at HSb (10%bv : bv 5) (w64 (dec_a_len (d_n cx))) P10
  ltac:(cbn [sv_denot]; rewrite ct_E_33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ct_reg_at HSb (26%bv : bv 5) (w64 (dec_a_len (d_n cx))) P26
  ltac:(cbn [sv_denot]; rewrite ct_E_33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ct_reg_at HSb (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x748)) P1 ltac:(apply codeptr_val; exact HEIb).
assert (Psp : spZ (ms_regs msB) = d_sp0 cx + (d_sp1 cx - d_sp0 cx)).
{ unfold spZ. rewrite (PK 2%bv ltac:(ct_in)).
  transitivity (bv_unsigned (YK11.getr (ms_regs msA) 2)); [f_equal; exact (HP2 2 ltac:(unfold acallee_saved; lia))|].
  unfold spZ in Qsp. exact Qsp. }
assert (P3 : YK11.getr (ms_regs msB) 3 = w64 (as_gp B)).
{ rewrite (PK 3%bv ltac:(ct_in)).
  transitivity (YK11.getr (ms_regs msA) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact Q3]. }
assert (P4 : YK11.getr (ms_regs msB) 4 = w64 (as_tp B)).
{ rewrite (PK 4%bv ltac:(ct_in)).
  transitivity (YK11.getr (ms_regs msA) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact Q4]. }
assert (Praok : YK0s.ret_ok (YK11.getr (ms_regs msB) 1))
  by (rewrite P1; apply (ret_ok_codeptr_v (PI := PI_decode)); [lia | reflexivity]).
(* the read-only view at the DEC_RO_RD bytes, at the call (W2, msB) and at the cut state (W, mem): rom_view at the
   entry (dec_a_rom), carried by each journal's image clause, which dec_ro_rd_scoped opens at every DEC_RO_RD byte.
   The mode's table words are DEC_RO_RD bytes, so dec_a_mode_ok is carried from the one state to the other through
   them (cmp_mode_re). *)
assert (HROMb : forall a, dec_in_ro_rd a ->
  aview segs (w_H W2) (ms_mem msB) a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 a))).
{ intros a Ha.
  pose proof HJbd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J3b & _).
  destruct (dec_ro_rd_rom_clean a Ha) as (Hrom & _).
  destruct (dec_ro_rd_scoped B HROS HRONE a Ha) as (Hno & Hne).
  rewrite J3b.
  - exact (HR a Hrom).
  - destruct Hrom as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
  - exact Hno.
  - exact Hne.
  - apply fp_spares_closed. exact sink_closed_nil. }
assert (HROM0 : forall a, dec_in_ro_rd a ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 a))).
{ intros a Ha.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J30 & _).
  destruct (dec_ro_rd_rom_clean a Ha) as (Hrom & _).
  destruct (dec_ro_rd_scoped B HROS HRONE a Ha) as (Hno & Hne).
  rewrite J30.
  - exact (HR a Hrom).
  - destruct Hrom as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
  - exact Hno.
  - exact Hne.
  - apply fp_spares_closed. exact sink_closed_nil. }
(* the word the leaf reads, UPSTREAM_DIV36_AT = decode_obj 9 (the ÷36 multiplier), is an owned constant cell of
   dec_crt_cells (its row picked by statement), read at the call state *)
assert (Hdiv : forall k, (k < 8)%nat ->
  aview segs (w_H W2) (ms_mem msB) (decode_obj 9%nat + Z.of_nat k) = Some (le_byte 0xe38e38e38e38e38f 8 k)).
{ pose proof (HCELLS ly2) as HCL.
  repeat match type of HCL with _ /\ _ => let H1 := fresh "Row" in destruct HCL as [H1 HCL] end.
  assert (Hrow : In (z8 (ANum (decode_obj 9%nat)) 0xe38e38e38e38e38f) (as_const B ly2)) by assumption.
  pose proof HJbd as (HARb & _). destruct HARb as [HARm _].
  pose proof (am_const _ _ _ _ HARm) as HC. rewrite Forall_forall in HC.
  exact (HC _ Hrow). }
assert (Hbytes : LMem.bytes_at segs (ms_mem msB) CChan.UPSTREAM_DIV36_AT (LMem.le8 (Z_to_bv 64 CChan.UPSTREAM_DIV36))).
{ split; [unfold CChan.UPSTREAM_DIV36_AT; lia|].
  split; [rewrite LMem.length_le8; unfold CChan.UPSTREAM_DIV36_AT; lia|].
  intros i Hi. rewrite LMem.length_le8 in Hi.
  assert (Hv : aview segs (w_H W2) (ms_mem msB) (CChan.UPSTREAM_DIV36_AT + Z.of_nat i) =
               Some (bv_unsigned (nth i (LMem.le8 (Z_to_bv 64 CChan.UPSTREAM_DIV36)) (Z_to_bv 8 0)))).
  { replace CChan.UPSTREAM_DIV36_AT with (decode_obj 9%nat) by (vm_compute; reflexivity).
    rewrite (Hdiv i Hi). f_equal. clear - Hi. do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. }
  destruct (dec_leafb_mrd_aview W2 (ms_mem msB) _ _ Hv) as (b & Hb & Hbv).
  rewrite Hb, (nth_error_nth' (LMem.le8 (Z_to_bv 64 CChan.UPSTREAM_DIV36)) (Z_to_bv 8 0))
    by (rewrite LMem.length_le8; exact Hi).
  f_equal. apply bv_eq. exact Hbv. }
assert (Hrng : LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W2) CChan.UPSTREAM_DIV36_AT 8).
{ apply (dec_leafb_rng W2); [unfold CChan.UPSTREAM_DIV36_AT; lia | unfold CChan.UPSTREAM_DIV36_AT; lia |].
  intros a Ha. replace a with (CChan.UPSTREAM_DIV36_AT + (a - CChan.UPSTREAM_DIV36_AT)) by lia.
  apply (dec_leafb_covers_visible (w_H W2) CChan.UPSTREAM_DIV36_AT 8);
    [exact (w_Hoff W2) | vm_compute; reflexivity | lia | unfold CChan.UPSTREAM_DIV36_AT; lia]. }
pmkst HSb.
assert (HPCU : decode_sigma DS_reac_upstream_channels = CChan.REAC_UPSTREAM_CHANNELS) by (vm_compute; reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (YK11.mkst rg (Z_to_bv 64 (decode_sigma DS_reac_upstream_channels)) mm rom) mdx) Q) end.
rewrite HPCU.
pose proof (LUC fx) as LU. unfold dec_leaf_at, LUpChannels.dec_reac_upstream_channels_cg in LU.
change SEGS with segs.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
  refine (@dec_leafb_journal fx rc dec_A_sink_head B LAWS W2 (ms_regs msB) (ms_mem msB) DEC_LLVMF_STK (d_sp0 cx) []
    (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 mdx (dec_ev_5fc + 1)
    (d_sp1 cx - d_sp0 cx) CChan.REAC_UPSTREAM_CHANNELS
    (Some (CChan.upstream_result (bv_unsigned (YK11.getr (ms_regs msB) (Z_to_bv 5 10))))) []
    (fun m2 => m2 = ms_mem msB) HJbd Psp Ho16 ltac:(lia) ltac:(lia) Praok P3 P4 _ _) end.
  - intros a Ha. inversion Ha.
  - intros HPRE. exact (LU ly2 S2 W2 (ms_regs msB) (ms_mem msB) _ HPRE Hbytes Hrng). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HRES & _ & _ & HX3).
subst mem3.
apply SRr_ret.
(* ---- +0x748: the post ---- *)
assert (VS : forall a, d_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W) mem a).
{ intros a Ha. rewrite HV2, (K1 a Ha). apply HV1. }
assert (VF : forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W) mem a).
{ intros a Ha. rewrite HV2, (K2 a Ha). apply HV1. }
assert (VSH : forall i, 0 <= i < 8 ->
  aview segs (w_H W2) (ms_mem msB) (d_SH cx + i) = aview segs (w_H W) mem (d_SH cx + i)).
{ intros i Hi. rewrite HV2, (K3 i Hi). apply HV1. }
assert (VB : forall b m i, List.In (b, m) (ablocks B ly1 S1) -> (b, m) <> (out, dec_a_olen nch ns) ->
  0 <= i < req_size m -> aview segs (w_H W2) (ms_mem msB) (b + i) = aview segs (w_H W) mem (b + i)).
{ intros b m i Hin Hne Hi. rewrite HV2, (K4 b m i Hin Hne Hi). apply HV1. }
assert (RK : forall r : Z, List.In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 27] ->
  YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hcs : acallee_saved r) by (unfold acallee_saved; cbn [List.In] in Hr; lia).
  assert (Hk2 : List.In (Z_to_bv 5 r) ct_keep2)
    by (cbn [List.In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr; ct_inb).
  assert (Hk1 : List.In (Z_to_bv 5 r) ct_keep1)
    by (cbn [List.In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr; ct_inb).
  rewrite (HP3 r Hcs), (PK _ Hk2), (HP2 r Hcs). exact (QK1 _ Hk1). }
unfold llvm_a_st_748.
exists fx, ly2, S2, regs3, (ms_mem msB), md3, res, mode, nch, ns.
(* the return address the leaf returned to (its post names it through the bridge's own register reader) *)
split; [lazymatch goal with |- mkCfg (YK11.mkst _ ?x _ _) _ = _ =>
  replace x with (w64 (DEC_A_LLVMF + 0x748)) by (rewrite Hpcw; symmetry; exact P1) end; reflexivity|].
split; [exact Hfrm|].
split.
{ unfold dec_a_core.
  split; [exact HJ3|].
  split; [rewrite Hfr2; exact Hfrs|].
  split; [transitivity (YK11.getr regs 8); [exact (RK 8 ltac:(ct_inz)) | exact R8]|].
  split; [transitivity (YK11.getr regs 9); [exact (RK 9 ltac:(ct_inz)) | exact R9]|].
  split; [unfold spZ; transitivity (bv_unsigned (YK11.getr regs 2));
    [f_equal; exact (RK 2 ltac:(ct_inz)) | exact Hsp]|].
  split; [exact Hsp240|]. split; [exact Hsp32|].
  split; [transitivity (YK11.getr regs 3); [exact (RK 3 ltac:(ct_inz)) | exact Rgp]|].
  split; [transitivity (YK11.getr regs 4); [exact (RK 4 ltac:(ct_inz)) | exact Rtp]|].
  split; [apply (ct_saved_kept cx (aview segs (w_H W) mem)); [intros a Ha; apply VS; lia | exact Hsaved]|].
  split; [exact HF4096|]. split; [exact HF32|].
  split.
  { intros a Ha.
    assert (Hfin3 : List.In (DEC_FCLASS, d_fpos cx) (frames S2)) by (rewrite Hfr2, Hfrs; left; reflexivity).
    pose proof HJ3 as (HAR3 & Hly3 & _).
    assert (EF3 : frame_addr ly2 DEC_FCLASS (d_fpos cx) = d_F cx).
    { destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). unfold d_F, frame_addr. rewrite EF. reflexivity. }
    destruct (al_frames _ _ LAWS _ _ _ _ _ DEC_FCLASS (d_fpos cx) HAR3 Hfin3) as (_ & _ & HFb & _).
    exact (proj1 (HFb a ltac:(rewrite EF3; change (fs_frame_bytes DEC_FCLASS) with 64; lia))). }
  split; [apply (ct_rdword_kept W W2 mem (ms_mem msB)); [intros k Hk; apply VF; lia | exact HFL]|].
  split.
  { intros Hn0. rewrite Hbl2. pose proof (Hblk Hn0) as Hin1. rewrite Hbl1 in Hin1.
    apply in_app_or in Hin1 as [Hin1 | [Heq | Hin1]].
    - apply in_or_app. left. exact Hin1.
    - exfalso. destruct Hpn as [[Hn0' _] | [_ Hinp]]; [lia|]. apply HnotO. rewrite Heq. exact Hinp.
    - apply in_or_app. right. exact Hin1. }
  apply (ct_garr8_kept W W2 mem (ms_mem msB) (d_p cx)); [|exact Hgarrp].
  intros k Hk. rewrite length_map in Hk.
  destruct Hpn as [[Hn0 _] | [Hn0 Hinp]]; [lia|].
  pose proof (Hblk ltac:(lia)) as Hin1.
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrq.
  apply (VB (d_p cx) (d_n cx) k Hin1); [|lia].
  intros Heq. apply HnotO. rewrite <- Heq. exact Hinp. }
split.
{ rewrite Hbl2.
  assert (HP12 : Permutation (l1 ++ l2) ((ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))]) ++ [])).
  { apply (Permutation_app_inv l1 l2 _ [] (out, dec_a_olen nch ns)). rewrite <- Hbl1. rewrite <- app_assoc.
    exact Hperm. }
  rewrite app_nil_r in HP12. exact HP12. }
split; [exact Hres4096|].
split; [unfold dec_spent_748; exact (mo_le_trans MT MTL _ _ _ _ _ Hmle MLE2)|].
split; [exact (mo_ok_step MT MTL S1 S2 (mo_free MT) (dec_rest_748 MT) Hmok MLE2)|].
split.
{ split; [transitivity (YK11.getr regs 19); [exact (RK 19 ltac:(ct_inz)) | exact Rs3]|].
  split; [transitivity (YK11.getr regs 21); [exact (RK 21 ltac:(ct_inz)) | exact Rs5]|].
  transitivity (YK11.getr regs 27); [exact (RK 27 ltac:(ct_inz)) | exact Rs11]. }
split.
{ pose proof (HRES _ eq_refl) as R10f.
  assert (P10z : YK11.getr (ms_regs msB) (Z_to_bv 5 10) = w64 (dec_a_len (d_n cx))) by exact P10.
  assert (Ul : bv_unsigned (w64 (dec_a_len (d_n cx))) = dec_a_len (d_n cx))
    by (unfold w64; apply unsigned_lit_small; lia).
  rewrite P10z, Ul in R10f. exact R10f. }
split; [transitivity (YK11.getr regs 18); [exact (RK 18 ltac:(ct_inz)) | exact Rs2]|].
split; [transitivity (YK11.getr regs 20); [exact (RK 20 ltac:(ct_inz)) | exact Rs4]|].
split; [transitivity (YK11.getr (ms_regs msB) 26); [exact (HP3 26 ltac:(unfold acallee_saved; lia)) | exact P26]|].
split; [apply (cmp_mode_re B cx W W2 mem (ms_mem msB) ly1 S1 md ly2 S2 md3 mode nch ns HCELLS HAR1 (proj1 HJ3) Hmode);
  [intros a Ha; rewrite (HROMb a Ha), (HROM0 a Ha); reflexivity | intros k Hk; apply VF; lia]|].
split.
{ pose proof Hfsh as (FS1 & FS4 & FS5 & FS6).
  split; [|split; [|split]].
  - intros i Hi. rewrite VSH by lia. exact (FS1 i Hi).
  - rewrite (VSH 4) by lia. exact FS4.
  - rewrite (VSH 5) by lia. exact FS5.
  - intros i Hi. rewrite VSH by lia. exact (FS6 i Hi). }
split.
{ apply (ct_garr8_kept W W2 mem (ms_mem msB) res); [|exact Hgarr].
  intros k Hk. rewrite length_map, Hblen in Hk.
  pose proof (req_size_pos (dec_a_len (d_n cx)) ltac:(lia)) as Hrq.
  apply (VB res (dec_a_len (d_n cx)) k HinR HRO). lia. }
split.
{ intros Hpok. destruct (Hguard Hpok) as (G8 & G16 & G24 & G48). unfold dec_a_slot in G8, G16, G24, G48 |- *.
  split; [|split; [|split]];
    (apply (ct_rdword_kept W W2 mem (ms_mem msB)); [intros k Hk; apply VS; lia|]); assumption. }
unfold dec_a_slot.
split; [apply (ct_rdword_kept W W2 mem (ms_mem msB)); [intros k Hk; apply VS; lia | exact Hsl40]|].
split; [apply (ct_rdword_kept W W2 mem (ms_mem msB)); [intros k Hk; apply VS; lia | exact Hsl56]|].
split; [apply (ct_rdword_kept W W2 mem (ms_mem msB)); [intros k Hk; apply VS; lia | exact Hsl64]|].
apply (ct_rdword_kept W W2 mem (ms_mem msB)); [intros k Hk; apply VS; lia | exact Hsl112].
Qed.

End body.

Lemma cmp_tail : @cmp_prem rc RA_LLVMF B MT -> forall (cx : dctx) (W : world decodesegs0) (c : config),
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_a_rom cx -> @cmp_q734 rc B MT cx W c -> SRr decodesegs0 W c (@llvm_a_st_748 rc B MT cx).
Proof.
intros HPREM cx W c HB HR H734.
pose proof H734 as H734c.
destruct H734c as (fx5 & ly5 & S5 & regs5 & mem5 & md5 & res & out & mode & nch & ns & Hc5 & _).
subst c.
exact (@ct_body fx5 cx W regs5 mem5 md5 HPREM HB HR H734).
Qed.

End cmpt.
