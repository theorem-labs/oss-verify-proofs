(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 329 of its 374 lines of code are new or changed and 1879 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickEpi.v, with its module paths and module names changed; 300 of its 350 lines of code are new or changed and 324 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op6m: Lemma lc_op6m_ok : lc_op6m_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment OP6M of the image-B walk of LLVMFuzzerTestOneInput: the one slot +0x8e8 of the listing
   lib/B/Prog/DgnTransportBList.v (pc 0x81b88), `jal m_set` with return address +0x8ec, from the cut MSET (+0x8e8) to the
   cut CLS (+0x8ec).

   What the code does. The slot is the call itself: no instruction runs before the jal, so the run from the cut is the
   one jal. It starts from a symbolic state with every register an atom and no region, so it reads and writes no byte:
   the call memory is the cut's (YC4b.v kept_of_frame) and every register but ra is the cut's. In particular a0 = S_CLOSED
   and a1 = R_CLOSED (the cut's own facts, set at +0x8e0 / +0x8e4), sp = s1 = sp1, gp and tp are the slot's, and ra is
   the return address +0x8ec.

   m_set is a G-form callee composed in the same G journal (no gx_call_cg): its statement lib/B/Prog/m_set_cg.v
   transport_m_set_cg is a premise of the walk (lp_mset), applied at the call state with SRr_bind. Its stack window is
   [sp1 - MSET_STK, sp1): sp1 mod 16 = 0 since sp1 mod 32 = 0 (the core), and the window lies inside the slot's stack
   (sp0 - 336 <= sp1, MSET_STK + 336 <= LLVMF_STK). Every byte it stores (m_set_cg.v mset_st_wr) is a byte of OW or of M,
   two rows of the world table, hence a byte of G and an image byte (DgnTransportBCg.v trans_g_img): apart from the
   caller's blocks and its class-2 frame (YCbq.v blk_img, frm_img), and below the frame's shadow bytes. What the call
   keeps (TransportGCg.v acall_kept_g) therefore carries the cut's core (LLVMFuzzerTestOneInput_st.v lc_core_kept, with
   the window MSET_STK and no event), its spill slots (lc_spills_kept: above sp1, outside the window) and the frame's 32
   shadow bytes (lc_fsh_kept); the presence of the frame's bytes goes over the call by YCbq.v apresent_transfer (frame
   bytes are not image bytes). The callee-saved registers come back by the post's aregs_preserved, so s2, s3, s4, s6,
   s8, s10 and s11 keep the cut's facts.

   The model. At op code 6 the operation is op_begin, m_close, diginet_session_close and settle
   (LLVMFuzzerTestOneInput_st.v lc_op6_eq); TSim/LoopOk.v op_ok at the start facts of the cut (lc_opok) says the chain
   answers Some, which names the world B2' of m_close_m B1. st.v lc_close_eq with the cut's lc_close_w B1 = Some B2
   turns that Some into m_set_m B2 S_CLOSED R_CLOSED = Some (B2', tt), the premise m_set's statement asks; its post gives
   the world relation at B2', which is what CLS carries with m_close_m B1 = Some (B2', tt). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The symbolic state at the cut: every register an atom, no region, no fact; no shadow token. *)
Definition m6_ss : sstate := mkSS LO_MSET sr_atoms [] None (mkFacts [] [] []).
Definition M6_Bx : sv := SLit 0.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac m6_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "m6_reg: no match for" T; fail
  end.
(* The write right of a run from a state with no region. *)
Ltac m6_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.
(* A run from a state with no region writes no byte. *)
Ltac m6_kept HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin; destruct Hin
  | ].

(* m_set's stores are bytes of OW or of M: bytes of G, between M's base and OW's end. *)
Lemma m6_wr_G : forall (Bw : list byte) (a : Z), mset_wr Bw a -> inG G_HARNESS_B a /\ TB_M <= a < TB_OW + TW.SZ_OW.
Proof.
intros Bw a Ha. unfold mset_wr, twb_fld in Ha.
unfold TW.A_OW_t_state, TW.A_OW_n, TW.A_M_state, TW.OW_t_ESZ, TC.TRANS_MAX in Ha.
destruct Ha as [[Hn Ha] | [Ha | Ha]].
- remember (TW.OW_n Bw) as n eqn:En. clear En.
  split; [|unfold TB_M, TB_OW, TW.SZ_OW, TW.OFF_OW in *; lia].
  unfold inG. apply Exists_exists. exists (TB_OW, TW.SZ_OW).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_OW) | unfold in_zr, TW.SZ_OW, TW.OFF_OW in *; cbn [fst snd]; lia].
- split; [|unfold TB_M, TB_OW, TW.SZ_OW, TW.OFF_OW in *; lia].
  unfold inG. apply Exists_exists. exists (TB_OW, TW.SZ_OW).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_OW) | unfold in_zr, TW.SZ_OW, TW.OFF_OW in *; cbn [fst snd]; lia].
- split; [|unfold TB_M, TB_OW, TW.SZ_OW, TW.OFF_M in *; lia].
  unfold inG. apply Exists_exists. exists (TB_M, TW.SZ_M).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_M) | unfold in_zr, TW.SZ_M, TW.OFF_M in *; cbn [fst snd]; lia].
Qed.

(* A range, from an index in it (plain arithmetic: the kit's lia prunes a hypothesis that holds req_size). *)
Lemma m6_rng : forall b i n : Z, 0 <= i < n -> b <= b + i < b + n.
Proof. intros b i n H. lia. Qed.

(* An index of a nonempty block is an index of its requested size. *)
Lemma m6_req : forall i n : Z, 0 < n -> 0 <= i < n -> 0 <= i < req_size n.
Proof. intros i n Hn Hi. unfold req_size. destruct (Z.eqb_spec n 0) as [E | _]; lia. Qed.

(* The frame's bytes and its shadow bytes are addresses (the shadow of a frame below the ceiling is below 2 ^ 64):
   the quotient is named, since the kit's lia drops a hypothesis that holds a division. *)
Lemma m6_addr_rng : forall F a c, 4096 <= F -> F + 256 <= c -> c <= 140737479966720 ->
  (F <= a < F + 256 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 32) -> 0 <= a < 2 ^ 64.
Proof.
intros F a c H0 H1 H2 Ha.
assert (HFc : F <= 140737479966720) by lia.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as D0.
pose proof (Z.div_le_mono F 140737479966720 8 ltac:(lia) HFc) as D1.
change (140737479966720 / 8) with 17592184995840 in D1.
remember (F / 8) as q eqn:Eq. clear Eq.
unfold SHADOW_OFF in *. change (2 ^ 64) with 18446744073709551616.
destruct Ha as [Ha | Ha]; lia.
Qed.

(* A shadow byte of the frame is above OW's end, hence no byte m_set stores. *)
Lemma m6_sh_hi : forall F a, 0 <= F -> SHADOW_OFF + F / 8 <= a -> a < TB_OW + TW.SZ_OW -> False.
Proof.
intros F a H0 H1 H2. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as D0.
remember (F / 8) as q eqn:Eq. clear Eq.
unfold SHADOW_OFF, TB_OW, TW.SZ_OW in *. lia.
Qed.

Section seg6m. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The walk's valuation: the 32 registers at the cut. *)
Definition m6_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma m6_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (m6_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold m6_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma m6_env_img : forall regs, img_env VAL A_LIM (m6_E regs).
Proof. intros regs. unfold m6_E. apply Eimg_env. Qed.
Lemma m6_agree : forall regs, env_agree 32 (Ereg regs []) (m6_E regs).
Proof. intros regs. split; [intros n Hn; unfold m6_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma lc_op6m_ok : lc_op6m_stmt B MT XL RLO RHI.
Proof.
unfold lc_op6m_stmt. intros HP cx op W c HB HMS.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_meter_laws B MT XL RLO RHI HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
destruct HMS as (ly1 & S1 & regs1 & mem1 & md1 & e1 & B1 & B2 & Hc & Hopc & HL & Hbeg & Hcw & Htw & R10 & R11 &
  Hcur & Hs46).
subst c.
pose proof HL as (HC & HFR & HSPL & HFSH & HOPOK & HEV & HMO & R19).
pose proof HOPOK as (HAG & HOPS & HFIO & HFN & HKOP).
pose proof (@lc_geom rc B MT XL RLO RHI cx ly1 S1 W regs1 mem1 md1 e1 HB HC) as GEO.
destruct GEO as [HARc Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof HFR as (R18 & R26).
pose proof Hs46 as (R20 & R22).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
change (2 ^ 47) with 140737488355328 in H47.
pose proof asan_consts as ((CVlo & CVhi) & _).
pose proof HB as (HAFN & Hra0 & Ha0 & Ha1 & Hpn & Hnl & Hgarr & Hfrs0 & Hev & Hlive & Hrod & Hsink & Hfd & Hfss &
  Hmeta & Hmok0).
(* ---- geometry, as closed arithmetic ---- *)
assert (HSTKFIT : MSET_STK + 336 <= LLVMF_STK) by (unfold MSET_STK, MSET_FRAME, LLVMF_STK; lia).
assert (Hsp1lo : alloc_ceiling + 32432 <= lc_sp1 cx) by exact Hsp1c.
assert (Hsp1hi : lc_sp1 cx <= lc_sp0 cx) by (unfold LF_FRAME in Hsp1; lia).
assert (Hsp0hi : lc_sp0 cx <= 2 ^ 47) by (unfold lc_sp0 in *; lia).
assert (Hsp1rg : 0 <= lc_sp1 cx < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
(* ---- the model: the operation's chain answers Some; its m_close is m_set at lc_close_w ---- *)
destruct (LOK.op_ok LP.links_holds timg_B (lo_ops op) (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op)
  HAG HOPS HFIO HFN ltac:(cbv beta; lia) ltac:(cbv beta; change (2 ^ 64) with 18446744073709551616; lia))
  as (Bz & cz & kz & EQ0 & _ & _).
rewrite (lc_op6_eq timg_B (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op) Hopc) in EQ0.
rewrite Hbeg in EQ0. cbv beta iota in EQ0.
destruct (TC.m_close_m B1) as [[B2' u2]|] eqn:ECL0; cbv beta iota in EQ0; [|discriminate EQ0].
clear EQ0 Bz cz kz.
assert (ECL : TC.m_close_m B1 = Some (B2', tt)) by (destruct u2; exact ECL0).
clear ECL0 u2.
assert (EMS : TC.m_set_m B2 TC.S_CLOSED TC.R_CLOSED = Some (B2', tt)).
{ rewrite <- ECL. rewrite (lc_close_eq B1), Hcw. reflexivity. }
(* ---- the symbolic state at the cut ---- *)
set (E := m6_E regs1) in *.
assert (HEI : img_env VAL A_LIM E) by apply m6_env_img.
assert (EWR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs1 r)
  by (intros nx rx Hnx; apply m6_ew_reg; exact Hnx).
assert (HS : st_ok_pi (fx := l_fx cx) segs VAL E m6_ss
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs1 (Z_to_bv 64 (BASE + LO_MSET)) mem1 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold m6_ss.
  apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I. }
assert (SHOK : sh_ok segs M6_Bx (@nil shent) E (mrestrict (w_H W) mem1)) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  G_HARNESS_B HGX 0 []) as RUN.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs1 (Z_to_bv 64 (BASE + LO_MSET)) mem1
    (YK11.seg_rom segs)) md1) Q) end.
(* ---- +0x8e8: `jal m_set` ---- *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ m6_awr. }
m6_kept HFr KR W mem1 ms.
assert (GR1 : forall a, apresent (w_H W) mem1 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the callee-saved registers are the cut's *)
assert (HPRE : aregs_preserved regs1 (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H W) E _ ms regs1 [] HS);
      [exact (m6_agree regs1) | vm_compute; reflexivity]).
(* the call's arguments and its return address *)
m6_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LO_CLS)) Q1 ltac:(apply codeptr_val; exact HEI).
m6_reg HS (10%bv : bv 5) (YK11.getr regs1 (10%bv : bv 5)) Q10
  ltac:(cbn [sv_denot]; rewrite (EWR 10%nat (10%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
m6_reg HS (11%bv : bv 5) (YK11.getr regs1 (11%bv : bv 5)) Q11
  ltac:(cbn [sv_denot]; rewrite (EWR 11%nat (11%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
assert (Q2 : YK11.getr (ms_regs ms) 2 = w64 (lc_sp1 cx))
  by exact (eq_trans (HPRE 2 ltac:(hnf; lia)) Rsp).
assert (QSP : spZ (ms_regs ms) = lc_sp1 cx)
  by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
(* the world relation at the call memory *)
assert (TWc : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) B2).
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem1)); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
  apply KR. lia. }
assert (EBR : BASE + LO_CLS = 0x81b8c) by (vm_compute; reflexivity).
(* ---- the call of m_set ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB_m_set)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ eapply (lp_mset B MT XL RLO RHI HP (l_fx cx)).
  - first [exact HJ | apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ].
  - rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold LO_CLS; lia | reflexivity].
  - unfold raZ. rewrite Q1, EBR. rewrite unsigned_lit_small by lia. lia.
  - exact (eq_trans (HPRE 3 ltac:(hnf; lia)) Rgp).
  - exact (eq_trans (HPRE 4 ltac:(hnf; lia)) Rtp).
  - exact (eq_trans Q10 R10).
  - exact (eq_trans Q11 R11).
  - rewrite QSP. pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1.
    rewrite Hsp1al, Z.add_0_r in D1. rewrite D1.
    replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring.
    apply Z.mod_mul. lia.
  - rewrite QSP. unfold LF_FRAME in Hsp1. lia.
  - rewrite QSP. lia.
  - exact TWc.
  - exact EMS.
  - unfold TC.S_CLOSED. change (2 ^ 31) with 2147483648. lia.
  - unfold TC.R_CLOSED. change (2 ^ 31) with 2147483648. lia.
  - unfold MSET_EV. rewrite Z.add_0_r. unfold RECV_EV in HEV. unfold EV_LIB in Hev.
    change TC.OPS_MAX with 1024 in HOPS. lia. }
cbv beta.
intros W3 c3 _ HPOST.
unfold transport_mset_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & Ec3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HTW3).
assert (Ee3 : e3 = 0) by (unfold MSET_EV in He3; lia). subst e3. rewrite Z.add_0_r in HJ3.
rewrite Q1 in Ec3.
(* ---- the cut CLS ---- *)
apply SRr_ret.
pose proof HK3 as (K31 & K32 & K33 & K34 & K35 & K36). rewrite QSP in K31.
(* the bytes of the call's written range are image bytes below the frame's shadow *)
assert (HWRG : forall a, mset_st_wr B2 TC.S_CLOSED a -> in_img segs a /\ a < TB_OW + TW.SZ_OW).
{ intros a (_ & Ha). destruct (m6_wr_G B2 a Ha) as (HaG & _ & Hhi).
  split; [exact (trans_g_img a HaG) | exact Hhi]. }
(* the frame's bytes are no bytes of the written range *)
assert (HNWF : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> ~ mset_st_wr B2 TC.S_CLOSED a).
{ intros a Ha Hx.
  exact (frm_img segs B LAWS ly1 S1 W mem1 md1 LF_CID (l_fpos cx) a HARc HFin
    ltac:(rewrite HFaddr; change (fs_frame_bytes LF_CID) with LF_FBYTES; lia) (proj1 (HWRG a Hx))). }
(* the frame's shadow bytes are no bytes of the written range *)
assert (HNWS : forall a, lc_SH cx <= a < lc_SH cx + 32 -> ~ mset_st_wr B2 TC.S_CLOSED a).
{ intros a Ha Hx. unfold lc_SH in Ha.
  exact (m6_sh_hi (lc_F cx) a ltac:(lia) (proj1 Ha) (proj2 (HWRG a Hx))). }
(* the frame's bytes and its shadow bytes as the call left them *)
assert (KFR : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W) (ms_mem ms) a).
{ intros a Ha.
  exact (K34 LF_CID (l_fpos cx) a HFin
    ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr;
          change (fs_frame_bytes LF_CID) with LF_FBYTES; lia) (HNWF a Ha)). }
assert (KSH : forall a, lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W) (ms_mem ms) a).
{ intros a Ha.
  exact (K34 LF_CID (l_fpos cx) a HFin
    ltac:(right; unfold in_zr; cbn [fst snd]; rewrite HFaddr;
          change (fs_frame_bytes LF_CID / 8) with 32; unfold lc_SH, shadow_addr in *; lia) (HNWS a Ha)). }
(* the core, the spill slots and the frame's shadow at the return *)
assert (KCORE : @lc_core rc B cx ly3 S3 W3 regs3 mem3 md3 e1).
{ apply (@lc_core_kept rc B MT XL RLO RHI cx ly1 S1 W regs1 mem1 md1 e1 MSET_STK
    ly3 S3 W3 regs3 mem3 md3 e1 HB HC).
  - exact HJ3.
  - exact Hfr3.
  - exact Hperm3.
  - intros r Hr. exact (eq_trans (HP3 r Hr) (HPRE r Hr)).
  - unfold MSET_STK, MSET_FRAME, LLVMF_STK. lia.
  - intros a Ha Hw. rewrite (K31 a Ha Hw). apply KR. lia.
  - intros i Hi.
    assert (Hn0 : 0 < l_n cx) by lia.
    pose proof (HINg Hn0) as Hb.
    assert (Hir : 0 <= i < req_size (l_n cx)) by exact (m6_req i (l_n cx) Hn0 Hi).
    assert (HBND : 0 <= l_p cx + i < 2 ^ 64).
    { destruct (al_blocks _ _ LAWS ly1 S1 W mem1 md1 (l_p cx) (l_n cx) HARc Hb) as (_ & _ & _ & Happ & _ & _).
      pose proof (app_addr_below_ceil (l_p cx + i)
        (in_app_addr _ _ _ Happ (m6_rng (l_p cx) i (req_size (l_n cx)) Hir))) as HAC.
      pose proof (@ASAN_CEIL_range rc) as (CRa & _).
      change (2 ^ 64) with 18446744073709551616. lia. }
    assert (HNW : ~ mset_st_wr B2 TC.S_CLOSED (l_p cx + i)).
    { intros Hx. exact (blk_img segs B LAWS ly1 S1 W mem1 md1 (l_p cx) (l_n cx) (l_p cx + i) HARc Hb
        (m6_rng (l_p cx) i (req_size (l_n cx)) Hir) (proj1 (HWRG (l_p cx + i) Hx))). }
    rewrite (K32 (l_p cx) (l_n cx) i Hb Hir HNW).
    apply KR. exact HBND.
  - intros a Ha.
    assert (Ha' : lc_F cx <= a < lc_F cx + LF_FBYTES) by (unfold LF_FBYTES in *; lia).
    rewrite (K34 LF_CID (l_fpos cx) a HFin
      ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr;
            change (fs_frame_bytes LF_CID) with LF_FBYTES; lia) (HNWF a Ha')).
    apply KR. exact (m6_addr_rng (lc_F cx) a alloc_ceiling HF4096 HFceil CVhi (or_introl Ha')).
  - intros a Ha Hp.
    apply (apresent_transfer segs (w_H W) (w_H W3) (ms_mem ms) mem3 a).
    + exact (m6_addr_rng (lc_F cx) a alloc_ceiling HF4096 HFceil CVhi ltac:(left; unfold LF_FBYTES in *; lia)).
    + exact (frm_img segs B LAWS ly1 S1 W mem1 md1 LF_CID (l_fpos cx) a HARc HFin
        ltac:(rewrite HFaddr; change (fs_frame_bytes LF_CID) with LF_FBYTES; lia)).
    + exact (KFR a Ha).
    + exact (GR1 a Hp). }
assert (KSPL : lc_spills cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W3) mem3)).
{ apply (lc_spills_kept cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W) mem1)).
  - intros o Ho. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as HV.
    rewrite Forall_forall in HV. pose proof (HV o Ho) as (_ & _ & Hlo & Hhi). split; lia.
  - intros a Ha. transitivity (aview segs (w_H W) (ms_mem ms) a).
    + exact (K31 a ltac:(change (2 ^ 64) with 18446744073709551616; lia) ltac:(lia)).
    + apply KR. change (2 ^ 64) with 18446744073709551616. lia.
  - exact HSPL. }
assert (KFSH : lc_fsh cx (aview segs (w_H W3) mem3) false false).
{ apply (lc_fsh_kept cx (aview segs (w_H W) mem1)).
  - intros a Ha. transitivity (aview segs (w_H W) (ms_mem ms) a).
    + exact (KSH a Ha).
    + apply KR. unfold lc_SH in Ha. exact (m6_addr_rng (lc_F cx) a alloc_ceiling HF4096 HFceil CVhi (or_intror Ha)).
  - exact HFSH. }
(* the registers the cut names *)
assert (KR18 : YK11.getr regs3 18 = w64 (lc_SH cx))
  by exact (eq_trans (HP3 18 ltac:(hnf; lia)) (eq_trans (HPRE 18 ltac:(hnf; lia)) R18)).
assert (KR26 : YK11.getr regs3 26 = w64 SHADOW_OFF)
  by exact (eq_trans (HP3 26 ltac:(hnf; lia)) (eq_trans (HPRE 26 ltac:(hnf; lia)) R26)).
assert (KR19 : YK11.getr regs3 19 = w64 (lo_ops op))
  by exact (eq_trans (HP3 19 ltac:(hnf; lia)) (eq_trans (HPRE 19 ltac:(hnf; lia)) R19)).
assert (KR20 : YK11.getr regs3 20 = w64 (lc_F cx + 32))
  by exact (eq_trans (HP3 20 ltac:(hnf; lia)) (eq_trans (HPRE 20 ltac:(hnf; lia)) R20)).
assert (KR22 : YK11.getr regs3 22 = w64 1)
  by exact (eq_trans (HP3 22 ltac:(hnf; lia)) (eq_trans (HPRE 22 ltac:(hnf; lia)) R22)).
assert (KCUR : lc_cur cx regs3 24 27 (lc_oc (l_pl cx) (lo_c op))).
{ destruct Hcur as (Hcur1 & Hcur2). split.
  - exact (eq_trans (HP3 24 ltac:(hnf; lia)) (eq_trans (HPRE 24 ltac:(hnf; lia)) Hcur1)).
  - exact (eq_trans (HP3 27 ltac:(hnf; lia)) (eq_trans (HPRE 27 ltac:(hnf; lia)) Hcur2)). }
(* the record *)
exists ly3, S3, regs3, mem3, md3, e1, B1, B2'.
split.
{ assert (EPCZ : BASE + LO_CLS = transportb_text + LO_CLS) by (vm_compute; reflexivity).
  rewrite Ec3. unfold lc_cfg, w64. rewrite EPCZ. reflexivity. }
split; [exact Hopc|].
split.
{ split; [exact KCORE|]. split; [exact (conj KR18 KR26)|]. split; [exact KSPL|]. split; [exact KFSH|].
  split; [exact HOPOK|]. split; [exact HEV|]. split; [|exact KR19].
  destruct HMO as (HMle & HMok). split.
  - replace (Z.of_nat (lo_k op) * lf_rcost MT) with (Z.of_nat (lo_k op) * lf_rcost MT + 0) by lia.
    exact (mo_le_trans MT MTL _ _ _ _ _ HMle Hmo3).
  - apply (mo_ok_step MT MTL S1 S3 0 ((TC.OPS_MAX - Z.of_nat (lo_k op)) * lf_rcost MT));
      [rewrite Z.add_0_l; exact HMok | exact Hmo3]. }
split; [exact Hbeg|].
split; [exact ECL|].
split.
{ unfold lc_tw. exact HTW3. }
split; [exact KCUR|].
split; [exact KR20 | exact KR22].
Qed.

End seg6m.
