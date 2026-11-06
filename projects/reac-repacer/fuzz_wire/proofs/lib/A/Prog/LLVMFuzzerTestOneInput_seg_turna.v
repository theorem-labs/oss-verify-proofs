(* LLVMFuzzerTestOneInput_seg_turna: u_turn_a_ok : u_turn_a_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   turn_a segment of image A's walk (+0xa4 .. +0xfc, the seven checks on f): the image-A twin of this unit's
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_turna.v (commit da4c55efd5b6), itself in the form of reac-repacer/fuzz_uci's
   lib/A/Prog/LLVMFuzzerTestOneInput_seg_turnb.v and _seg_turnb_lib.v (commit 14922e68e3b0): a run of the Pa engine
   to a call, the callee's caller-journal contract (the record u_prem) at the call, the cut state rebuilt at the return
   address. Image A's offsets, its modules (lib/A, lib/Reusable) and its segment library (lib/A/Prog/WirePPa.v,
   WirePPaImg.v, WirePPaLib.v, PaJournal.v, LLVMFuzzerTestOneInput_seg_lib.v).

   The code (image A, the objdump of record; offsets from 0x7fe58): seven stretches, each of `mv` (addi rd, rs, 0)
   and one `jal`, no branch, no memory access:
     +0xa4  a0 = s0 (f), a1 = s1 (fn), a2 = s5 (bcast), `jal check_forward` at +0xb0; return +0xb4;
     +0xb4  a0 = f, a1 = fn, `jal check_ret` at +0xbc; return +0xc0;
     +0xc0  a0 = f, a1 = fn, `jal check_downstream` at +0xc8; return +0xcc;
     +0xcc  a0 = f, a1 = fn, `jal check_meter` at +0xd4; return +0xd8;
     +0xd8  a0 = f, a1 = fn, `jal check_counter` at +0xe0; return +0xe4;
     +0xe4  a0 = fn, `jal check_width` at +0xe8; return +0xec;
     +0xec  a0 = f, a1 = fn, a2 = s2 (slot), `jal check_read` at +0xf8; return +0xfc.
   Each run starts from a seat with no memory region (the stretch reads and writes no memory), so it keeps the memory
   and every callee-saved register (ta_to_call). Each call (ta_call) takes the callee's post: the journal grows by the
   callee's events, the blocks are kept up to Permutation, the saved words (at or above sp1, above the callee's stack
   window) and f's bytes (a caller block) are kept by acall_kept with no written range, the callee-saved registers
   are kept (aregs_preserved), and the meter is charged nothing (mo_le 0). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YE00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YE01 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaBase PaJournal WirePSyms WirePList WirePAddr
  WirePPa WirePPaLib WirePImg WirePPaImg WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require check_forward_cg check_ret_cg check_downstream_cg
  check_meter_cg check_counter_cg check_width_cg check_read_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module PFWD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_forward_cg.
Module PRET := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_ret_cg.
Module PDS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_downstream_cg.
Module PMET := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_meter_cg.
Module PCNT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_counter_cg.
Module PWID := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_width_cg.
Module PRD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.check_read_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. Small facts                                                       *)
(* ------------------------------------------------------------------ *)

(* A callee-saved register through aregs_preserved. *)
Lemma ta_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr regs2 r = YK11.getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac ta_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let x := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with x; unfold acallee_saved; lia end.
(* A register in a literal list of registers. *)
Ltac ta_in := cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).
Lemma ta_soff_denot : forall E (a : nat) w, ew E a = w -> sv_denot E (SOff a 0) = w.
Proof. intros E a w Ha. cbn [sv_denot]. rewrite Ha, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* The seat of every run: the registers as atoms, no memory region, no fact. *)
Definition ta_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Section seat. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ wire_listing PI_wire).
Local Abbreviation VAL := (@pa_val _ wire_listing PI_wire).
Local Abbreviation BASE := (@pa_val _ wire_listing PI_wire A_TEXT).
Lemma ta_seat : forall pc (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (Eimg (PI := PI_wire) (Ereg regs [])) (ta_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem.
rewrite restrict_mkst_fx. unfold ta_ss.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. exact I.
- exact (conj I (conj I I)).
Qed.
End seat.

(* A register's symbolic value at a state (st_ok_pi, or st_ok at a call). *)
Ltac ta_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok ?sg ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
(* The write rights of a run with no region. *)
Ltac ta_awr_ro :=
  lazymatch goal with |- awr_ok ?Ey ?rsx ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ey rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ].
(* The model after a run, named. *)
Ltac ta_md md2 :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) in *; clearbody md2 end.

Section ta. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).
Local Abbreviation U_C_F := (LLVMFuzzerTestOneInput_segs.U_C_F MT).

(* ------------------------------------------------------------------ *)
(* 2. The cut state between the calls                                  *)
(* ------------------------------------------------------------------ *)

(* The state at off with k events: u_st_oh's form (u_st_oh cx = ta_st cx U_OH U_EV_OH, u_st_pre cx =
   ta_st cx U_PRE U_EV_PRE). *)
Definition ta_st (cx : ucx) (off k : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (f : Z),
    c' = u_cfg cx off regs' mem' md' /\
    0 < u_n cx /\
    u_core B cx ly' S' W' regs' mem' md' [(f, u_fsz cx)] k /\
    u_meter MT XL cx S' (U_C_F cx) /\
    u_fregs cx regs' f /\
    garr8 segs (rd W' mem') f (map (fun b : byte => bv_unsigned b) (u_fb cx)).

(* What every call reads from the slot pre. *)
Lemma ta_base : forall cx, u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  Z.of_nat (length (u_pl cx)) = u_n cx /\
  st_nev (u_S cx) + EV_LIB <= EV_MAX /\
  arodata_okS segs B RLO RHI (aview segs (w_H (u_W cx)) (u_mem cx)).
Proof.
intros cx HP HB. unfold u_base, tfib_lib_pre_x in HB.
destruct HB as (_ & _ & _ & _ & _ & Hlen & _ & _ & Hnev & _ & Haro & _).
exact (conj (eq_sym Hlen) (conj Hnev Haro)).
Qed.

Lemma ta_J_facts : forall cx ly' S' W mem md k,
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md k ->
  u_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= u_sp0 cx /\ u_sp0 cx <= 2 ^ 47.
Proof.
intros cx ly' S' W mem md k HJ.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (H16 & _ & Hceil & Hlo & Hhi & H47 & _).
refine (conj H16 (conj _ _)); lia.
Qed.

(* The read-only bytes check_width and check_read read: the slot pre's arodata_okS, kept by the journal's image
   clause. *)
Lemma ta_rom_at : forall cx ly' S' W mem md k,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md k ->
  wire_rom_view_rd W mem.
Proof.
intros cx ly' S' W mem md k HP HB HJ a Ha.
pose proof (up_ro_unowned _ _ _ _ _ HP) as HOU. pose proof (up_rom_no_errno _ _ _ _ _ HP) as HNE.
destruct (ta_base cx HP HB) as (_ & _ & Haro).
destruct (wire_ro_rd_scoped B HOU HNE a Ha) as [Ho He].
destruct (wire_ro_rd_rom_clean a Ha) as [Hrom _].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img segs a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
rewrite (F3 a Himg Ho He (fp_spares_closed [] a sink_closed_nil)).
apply Haro; [left; exact Hrom | exact Ho | exact He].
Qed.

(* The saved words lie in [sp0 - 64, sp0): a reader that keeps those bytes keeps them. *)
Lemma ta_saved_kept : forall cx (r r' : reader), u_saved cx r ->
  (forall a, u_sp0 cx - 64 <= a < u_sp0 cx -> r' a = r a) -> u_saved cx r'.
Proof.
intros cx r r' Hs Hk. unfold u_saved in *. rewrite Forall_forall in *. intros o Ho.
rewrite <- (Hs o Ho). apply rdword_kept. intros i Hi.
assert (Hf : 8 <= fst o <= 64).
{ unfold wire_saved_at in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply Hk. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. A call by its contract                                            *)
(* ------------------------------------------------------------------ *)

(* The post every check contract of the turn states (check_forward_cg.v wire_cf_post and its six twins), at the
   caller's journal of the walk: EV events, the stack window STKc below the call's sp. *)
Definition ta_cpost (cx : ucx) (EV STKc : Z) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst (u_fx cx) regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly2 S2 W2 mem2 md2 (k + EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - STKc) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The one call lemma: a callee whose contract gives ta_cpost at the call leaves the cut state ta_st at the return
   address ret, with its EV events added. *)
Lemma ta_call : forall cx (W : world segs) regs mem md ly' S' k f ret EV STKc callee,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k -> u_meter MT XL cx S' (U_C_F cx) -> u_fregs cx regs f ->
  garr8 segs (rd W mem) f (map (fun b : byte => bv_unsigned b) (u_fb cx)) ->
  YK11.getr regs 1 = w64 (WIRE_A_LLVMF + ret) -> 0 <= STKc ->
  SRr segs W (@cfg_at (u_fx cx) segs callee regs mem md) (ta_cpost cx EV STKc ly' S' W mem k regs) ->
  SRr segs W (@cfg_at (u_fx cx) segs callee regs mem md) (ta_st cx ret (k + EV)).
Proof.
intros cx W regs mem md ly' S' k f ret EV STKc callee HP HB Hn HC (Hle & Hmo) HF Hg R1 HSTK HRUN.
pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
destruct (ta_base cx HP HB) as (Hlen & _ & _).
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm).
destruct (ta_J_facts _ _ _ _ _ _ _ HJ) as (H16 & Hceil & H47).
pose proof alloc_ceiling_val as Hce.
destruct (u_fn_range cx Hn) as (Hfn & Hfsz).
pose proof (u_fb_length cx Hn (eq_sym Hlen)) as Hfbl.
eapply SRr_mono; [exact HRUN|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hfr2 & Hperm2 & HK & Hmle).
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regs r)
  by (intros r Hr; exact (ta_pres regs regs2 r HPr Hr)).
assert (KV : forall a, u_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. destruct HK as (K1 & _). apply K1; [unfold u_sp1, U_FRAME, LLVMF_STK in *; lia | rewrite Hsp; lia]. }
assert (Hin : In (f, u_fsz cx) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
exists ly2, S2, regs2, mem2, md2, f.
refine (conj _ (conj Hn (conj _ (conj _ (conj _ _))))).
- unfold u_cfg. rewrite R1. reflexivity.
- refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
  + rewrite Hfr2. exact Hfrs.
  + unfold spZ in *. rewrite (P 2%bv ltac:(ta_cs)). exact Hsp.
  + rewrite (P 3%bv ltac:(ta_cs)). exact Hgp.
  + rewrite (P 4%bv ltac:(ta_cs)). exact Htp.
  + rewrite (P 23%bv ltac:(ta_cs)). exact H23.
  + rewrite (P 24%bv ltac:(ta_cs)). exact H24.
  + rewrite (P 25%bv ltac:(ta_cs)). exact H25.
  + rewrite (P 26%bv ltac:(ta_cs)). exact H26.
  + rewrite (P 27%bv ltac:(ta_cs)). exact H27.
  + apply (ta_saved_kept cx _ _ Hsv). intros a Ha. apply KV. unfold u_sp1, U_FRAME, LLVMF_STK in *. lia.
  + exact (Permutation_trans Hperm2 Hperm).
- split.
  + apply (mo_le_mono MT ML _ _ _ _ (mo_le_trans MT ML _ _ _ _ _ Hle Hmle)). lia.
  + apply (mo_ok_step MT ML S' S2 0); [|exact Hmle]. rewrite Z.add_0_l. exact Hmo.
- destruct HF as (R8 & R9 & R18 & R19 & R21 & R22). unfold u_fregs.
  rewrite (P 8%bv ltac:(ta_cs)), (P 9%bv ltac:(ta_cs)), (P 18%bv ltac:(ta_cs)), (P 19%bv ltac:(ta_cs)),
    (P 21%bv ltac:(ta_cs)), (P 22%bv ltac:(ta_cs)).
  exact (conj R8 (conj R9 (conj R18 (conj R19 (conj R21 R22))))).
- apply (garr8_kept segs (w_H W) (w_H W2) mem mem2 f); [|exact Hg].
  intros j Hj. rewrite length_map, Hfbl in Hj.
  destruct HK as (_ & K2 & _).
  apply (K2 f (u_fsz cx) j Hin); [|intros []].
  pose proof (req_size_pos (u_fsz cx) ltac:(lia)).
  assert (u_fn cx <= u_fsz cx) by (unfold u_fsz; lia). lia.
Qed.

(* What the premises of every check contract read at the call, from the cut state. *)
Lemma ta_pre : forall cx (W : world segs) regs mem md ly' S' k f ret,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k ->
  YK11.getr regs 1 = w64 (WIRE_A_LLVMF + ret) -> In ret [0xb4; 0xc0; 0xcc; 0xd8; 0xe4; 0xec; 0xfc] ->
  k <= U_EV_PRE ->
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  spZ regs mod 16 = 0 /\ (forall STKc, 0 <= STKc <= 0x2000 -> u_sp0 cx - LLVMF_STK <= spZ regs - STKc) /\
  spZ regs <= u_sp0 cx /\
  Z.of_nat (length (u_fb cx)) = u_fn cx /\ 0 <= u_fn cx <= 1600 /\
  (0 < u_fn cx -> exists bA nA, In (bA, nA) (ablocks B ly' S') /\ bA <= f /\ f + u_fn cx <= bA + nA) /\
  frames S' = [] /\
  st_nev (u_S cx) + k <= EV_MAX /\
  wire_rom_view_rd W mem.
Proof.
intros cx W regs mem md ly' S' k f ret HP HB Hn HC R1 Hret Hk.
destruct (ta_base cx HP HB) as (Hlen & Hnev & _).
pose proof HC as (HJ & Hfrs & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & Hperm).
destruct (ta_J_facts _ _ _ _ _ _ _ HJ) as (H16 & Hceil & H47).
pose proof alloc_ceiling_val as Hce.
destruct (u_fn_range cx Hn) as (Hfn & Hfsz).
assert (Hraz : raZ regs = WIRE_A_LLVMF + ret)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small;
      cbn [In] in Hret; repeat destruct Hret as [<- | Hret]; try destruct Hret; vm_compute; split; congruence).
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hfrs (conj _ _)))))))))).
- rewrite R1. cbn [In] in Hret. repeat destruct Hret as [<- | Hret]; try destruct Hret; vm_compute; reflexivity.
- rewrite Hraz. cbn [In] in Hret. repeat destruct Hret as [<- | Hret]; try destruct Hret; vm_compute; discriminate.
- rewrite Hsp. unfold u_sp1, U_FRAME. lia.
- intros STKc HS. rewrite Hsp. unfold u_sp1, U_FRAME, LLVMF_STK in *. lia.
- rewrite Hsp. unfold u_sp1, U_FRAME. lia.
- exact (u_fb_length cx Hn (eq_sym Hlen)).
- unfold WIRE_RECV_MAX in Hfn. lia.
- intros _. exists f, (u_fsz cx). split; [|unfold u_fsz; lia].
  apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity.
- unfold U_EV_PRE, U_EV_OH, PFWD.CF_EV, PRET.CR_EV, PDS.CDS_EV, PMET.CM_EV, PCNT.CK_EV, PWID.CW_EV, PRD.CRD_EV,
    EV_LIB, EV_MAX in *. lia.
- exact (ta_rom_at cx ly' S' W mem md k HP HB HJ).
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The seven checks                                                  *)
(* ------------------------------------------------------------------ *)

Ltac ta_open HP HB Hn HC R1 Hret Hk :=
  let HRA := fresh "HRA" in let H4K := fresh "H4K" in let H16 := fresh "H16" in let HWIN := fresh "HWIN" in
  let HSP0 := fresh "HSP0" in let Hfbl := fresh "Hfbl" in let Hfn := fresh "Hfn" in let Hblk := fresh "Hblk" in
  let Hfrs := fresh "Hfrs" in let Hnev := fresh "Hnev" in let Hrom := fresh "Hrom" in
  destruct (ta_pre _ _ _ _ _ _ _ _ _ _ HP HB Hn HC R1 Hret Hk)
    as (HRA & H4K & H16 & HWIN & HSP0 & Hfbl & Hfn & Hblk & Hfrs & Hnev & Hrom).

Lemma ta_cfwd : forall cx (W : world segs) regs mem md ly' S' k f,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k -> u_meter MT XL cx S' (U_C_F cx) -> u_fregs cx regs f ->
  garr8 segs (rd W mem) f (map (fun b : byte => bv_unsigned b) (u_fb cx)) -> k <= U_EV_PRE ->
  YK11.getr regs 1 = w64 (WIRE_A_LLVMF + 0xb4) ->
  YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 (u_fn cx) -> YK11.getr regs 12 = w64 (u_bc cx) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS_check_forward) regs mem md) (ta_st cx 0xb4 (k + PFWD.CF_EV)).
Proof.
intros cx W regs mem md ly' S' k f HP HB Hn HC HM HF Hg Hk R1 R10 R11 R12.
assert (Hret : In 0xb4 [0xb4; 0xc0; 0xcc; 0xd8; 0xe4; 0xec; 0xfc]) by ta_in.
ta_open HP HB Hn HC R1 Hret Hk.
pose proof HC as (HJ & _ & _ & Hgp & Htp & _).
apply (ta_call cx W regs mem md ly' S' k f 0xb4 PFWD.CF_EV PFWD.CF_STK _ HP HB Hn HC HM HF Hg R1
  ltac:(unfold PFWD.CF_STK, PFWD.CF_FRAME, ESTACK; lia)).
exact (up_cfwd _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
  ly' S' W mem md k regs f (u_fn cx) (u_bc cx) (u_fb cx) HJ HRA H4K Hgp Htp R10 R11 R12 H16
  (HWIN PFWD.CF_STK ltac:(unfold PFWD.CF_STK, PFWD.CF_FRAME, ESTACK; lia)) HSP0
  ltac:(unfold PFWD.CF_N_MAX; lia) Hfbl (u_bc_range cx) Hblk Hg
  ltac:(unfold PFWD.CF_EV; lia)).
Qed.

Lemma ta_cret : forall cx (W : world segs) regs mem md ly' S' k f,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k -> u_meter MT XL cx S' (U_C_F cx) -> u_fregs cx regs f ->
  garr8 segs (rd W mem) f (map (fun b : byte => bv_unsigned b) (u_fb cx)) -> k <= U_EV_PRE ->
  YK11.getr regs 1 = w64 (WIRE_A_LLVMF + 0xc0) ->
  YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 (u_fn cx) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS_check_ret) regs mem md) (ta_st cx 0xc0 (k + PRET.CR_EV)).
Proof.
intros cx W regs mem md ly' S' k f HP HB Hn HC HM HF Hg Hk R1 R10 R11.
assert (Hret : In 0xc0 [0xb4; 0xc0; 0xcc; 0xd8; 0xe4; 0xec; 0xfc]) by ta_in.
ta_open HP HB Hn HC R1 Hret Hk.
pose proof HC as (HJ & _ & _ & Hgp & Htp & _).
apply (ta_call cx W regs mem md ly' S' k f 0xc0 PRET.CR_EV PRET.CR_STK _ HP HB Hn HC HM HF Hg R1
  ltac:(unfold PRET.CR_STK, PRET.CR_FRAME, ESTACK; lia)).
exact (up_cret _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
  ly' S' W mem md k regs f (u_fn cx) (u_fb cx) HJ HRA H4K Hgp Htp R10 R11 H16
  (HWIN PRET.CR_STK ltac:(unfold PRET.CR_STK, PRET.CR_FRAME, ESTACK; lia)) HSP0
  ltac:(lia) Hfbl Hblk Hg
  ltac:(unfold PRET.CR_EV; lia)).
Qed.

Lemma ta_cds : forall cx (W : world segs) regs mem md ly' S' k f,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k -> u_meter MT XL cx S' (U_C_F cx) -> u_fregs cx regs f ->
  garr8 segs (rd W mem) f (map (fun b : byte => bv_unsigned b) (u_fb cx)) -> k <= U_EV_PRE ->
  YK11.getr regs 1 = w64 (WIRE_A_LLVMF + 0xcc) ->
  YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 (u_fn cx) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS_check_downstream) regs mem md) (ta_st cx 0xcc (k + PDS.CDS_EV)).
Proof.
intros cx W regs mem md ly' S' k f HP HB Hn HC HM HF Hg Hk R1 R10 R11.
assert (Hret : In 0xcc [0xb4; 0xc0; 0xcc; 0xd8; 0xe4; 0xec; 0xfc]) by ta_in.
ta_open HP HB Hn HC R1 Hret Hk.
pose proof HC as (HJ & _ & _ & Hgp & Htp & _).
apply (ta_call cx W regs mem md ly' S' k f 0xcc PDS.CDS_EV PDS.CDS_STK _ HP HB Hn HC HM HF Hg R1
  ltac:(unfold PDS.CDS_STK, PDS.CDS_FRAME, ESTACK; lia)).
exact (up_cds _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
  ly' S' W mem md k regs f (u_fn cx) (u_fb cx) HJ HRA H4K Hgp Htp R10 R11 H16
  (HWIN PDS.CDS_STK ltac:(unfold PDS.CDS_STK, PDS.CDS_FRAME, ESTACK; lia)) HSP0
  ltac:(unfold PDS.CDS_N_MAX; lia) Hfbl Hblk Hg
  ltac:(unfold PDS.CDS_EV; lia)).
Qed.

Lemma ta_cmet : forall cx (W : world segs) regs mem md ly' S' k f,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k -> u_meter MT XL cx S' (U_C_F cx) -> u_fregs cx regs f ->
  garr8 segs (rd W mem) f (map (fun b : byte => bv_unsigned b) (u_fb cx)) -> k <= U_EV_PRE ->
  YK11.getr regs 1 = w64 (WIRE_A_LLVMF + 0xd8) ->
  YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 (u_fn cx) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS_check_meter) regs mem md) (ta_st cx 0xd8 (k + PMET.CM_EV)).
Proof.
intros cx W regs mem md ly' S' k f HP HB Hn HC HM HF Hg Hk R1 R10 R11.
assert (Hret : In 0xd8 [0xb4; 0xc0; 0xcc; 0xd8; 0xe4; 0xec; 0xfc]) by ta_in.
ta_open HP HB Hn HC R1 Hret Hk.
pose proof HC as (HJ & _ & _ & Hgp & Htp & _).
apply (ta_call cx W regs mem md ly' S' k f 0xd8 PMET.CM_EV PMET.CM_STK _ HP HB Hn HC HM HF Hg R1
  ltac:(unfold PMET.CM_STK, PMET.CM_FRAME, PMET.CM_ALIGN, ESTACK; lia)).
exact (up_cmet _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
  ly' S' W mem md k regs f (u_fn cx) (u_fb cx) HJ HRA H4K Hgp Htp R10 R11 H16
  (HWIN PMET.CM_STK ltac:(unfold PMET.CM_STK, PMET.CM_FRAME, PMET.CM_ALIGN, ESTACK; lia)) HSP0
  Hfbl Hblk Hg ltac:(rewrite Hfrs; vm_compute; reflexivity)
  ltac:(unfold PMET.CM_EV; lia)).
Qed.

Lemma ta_ccnt : forall cx (W : world segs) regs mem md ly' S' k f,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k -> u_meter MT XL cx S' (U_C_F cx) -> u_fregs cx regs f ->
  garr8 segs (rd W mem) f (map (fun b : byte => bv_unsigned b) (u_fb cx)) -> k <= U_EV_PRE ->
  YK11.getr regs 1 = w64 (WIRE_A_LLVMF + 0xe4) ->
  YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 (u_fn cx) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS_check_counter) regs mem md) (ta_st cx 0xe4 (k + PCNT.CK_EV)).
Proof.
intros cx W regs mem md ly' S' k f HP HB Hn HC HM HF Hg Hk R1 R10 R11.
assert (Hret : In 0xe4 [0xb4; 0xc0; 0xcc; 0xd8; 0xe4; 0xec; 0xfc]) by ta_in.
ta_open HP HB Hn HC R1 Hret Hk.
pose proof HC as (HJ & _ & _ & Hgp & Htp & _).
apply (ta_call cx W regs mem md ly' S' k f 0xe4 PCNT.CK_EV PCNT.CK_STK _ HP HB Hn HC HM HF Hg R1
  ltac:(unfold PCNT.CK_STK, PCNT.CK_FRAME, ESTACK; lia)).
exact (up_ccnt _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
  ly' S' W mem md k regs f (u_fn cx) (u_fb cx) HJ HRA H4K Hgp Htp R10 R11 H16
  (HWIN PCNT.CK_STK ltac:(unfold PCNT.CK_STK, PCNT.CK_FRAME, ESTACK; lia)) HSP0
  ltac:(lia) Hfbl Hblk Hg
  ltac:(unfold PCNT.CK_EV; lia)).
Qed.

Lemma ta_cwid : forall cx (W : world segs) regs mem md ly' S' k f,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k -> u_meter MT XL cx S' (U_C_F cx) -> u_fregs cx regs f ->
  garr8 segs (rd W mem) f (map (fun b : byte => bv_unsigned b) (u_fb cx)) -> k <= U_EV_PRE ->
  YK11.getr regs 1 = w64 (WIRE_A_LLVMF + 0xec) ->
  YK11.getr regs 10 = w64 (u_fn cx) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS_check_width) regs mem md) (ta_st cx 0xec (k + PWID.CW_EV)).
Proof.
intros cx W regs mem md ly' S' k f HP HB Hn HC HM HF Hg Hk R1 R10.
assert (Hret : In 0xec [0xb4; 0xc0; 0xcc; 0xd8; 0xe4; 0xec; 0xfc]) by ta_in.
ta_open HP HB Hn HC R1 Hret Hk.
pose proof HC as (HJ & _ & _ & Hgp & Htp & _).
apply (ta_call cx W regs mem md ly' S' k f 0xec PWID.CW_EV PWID.CW_STK _ HP HB Hn HC HM HF Hg R1
  ltac:(unfold PWID.CW_STK, PWID.CW_FRAME, ESTACK; lia)).
exact (up_cwid _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
  ly' S' W mem md k regs (u_fn cx) HJ HRA H4K Hgp Htp R10 H16
  (HWIN PWID.CW_STK ltac:(unfold PWID.CW_STK, PWID.CW_FRAME, ESTACK; lia)) HSP0
  ltac:(unfold PWID.CW_N_MAX; lia) Hrom
  ltac:(unfold PWID.CW_EV; lia)).
Qed.

Lemma ta_crd : forall cx (W : world segs) regs mem md ly' S' k f,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k -> u_meter MT XL cx S' (U_C_F cx) -> u_fregs cx regs f ->
  garr8 segs (rd W mem) f (map (fun b : byte => bv_unsigned b) (u_fb cx)) -> k <= U_EV_PRE ->
  YK11.getr regs 1 = w64 (WIRE_A_LLVMF + 0xfc) ->
  YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 (u_fn cx) -> YK11.getr regs 12 = w64 (u_slot cx) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS_check_read) regs mem md) (ta_st cx 0xfc (k + PRD.CRD_EV)).
Proof.
intros cx W regs mem md ly' S' k f HP HB Hn HC HM HF Hg Hk R1 R10 R11 R12.
assert (Hret : In 0xfc [0xb4; 0xc0; 0xcc; 0xd8; 0xe4; 0xec; 0xfc]) by ta_in.
ta_open HP HB Hn HC R1 Hret Hk.
pose proof HC as (HJ & _ & _ & Hgp & Htp & _).
apply (ta_call cx W regs mem md ly' S' k f 0xfc PRD.CRD_EV PRD.CRD_STK _ HP HB Hn HC HM HF Hg R1
  ltac:(unfold PRD.CRD_STK, PRD.CRD_FRAME, PRD.CRD_ALIGN, ESTACK; lia)).
exact (up_crd _ _ _ _ _ HP (u_fx cx) LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
  ly' S' W mem md k regs f (u_fn cx) (u_slot cx) (u_fb cx) HJ HRA H4K Hgp Htp R10 R11 R12 H16
  (HWIN PRD.CRD_STK ltac:(unfold PRD.CRD_STK, PRD.CRD_FRAME, PRD.CRD_ALIGN, ESTACK; lia)) HSP0
  ltac:(unfold PRD.W_RECV_MAX; lia) Hfbl (u_slot_int cx) Hblk Hg
  ltac:(rewrite Hfrs; vm_compute; reflexivity) Hrom
  ltac:(unfold PRD.CRD_EV; lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The runs between the calls                                        *)
(* ------------------------------------------------------------------ *)

(* The seven stretches: (head, return address of the call, callee, the argument registers and their values). *)
Definition ta_calls (cx : ucx) (f : Z) : list (Z * Z * Z * list (bv 5 * Z)) :=
  [(0xa4, 0xb4, wire_sigma WS_check_forward, [(10%bv, f); (11%bv, u_fn cx); (12%bv, u_bc cx)]);
   (0xb4, 0xc0, wire_sigma WS_check_ret, [(10%bv, f); (11%bv, u_fn cx)]);
   (0xc0, 0xcc, wire_sigma WS_check_downstream, [(10%bv, f); (11%bv, u_fn cx)]);
   (0xcc, 0xd8, wire_sigma WS_check_meter, [(10%bv, f); (11%bv, u_fn cx)]);
   (0xd8, 0xe4, wire_sigma WS_check_counter, [(10%bv, f); (11%bv, u_fn cx)]);
   (0xe4, 0xec, wire_sigma WS_check_width, [(10%bv, u_fn cx)]);
   (0xec, 0xfc, wire_sigma WS_check_read, [(10%bv, f); (11%bv, u_fn cx); (12%bv, u_slot cx)])].

(* An argument register after a run: a register the run copied from s0, s1, s2 or s5 (u_fregs). *)
Ltac ta_arg HS EL R8 R9 R18 R21 :=
  lazymatch goal with |- YK11.getr _ ?r = _ =>
    let Hr := fresh "Hr" in ta_reg HS r Hr; cbn [ms_regs restrict] in Hr; rewrite Hr;
    first [ rewrite (ta_soff_denot _ 8 _ (EL 8%nat 8%bv eq_refl)); exact R8
          | rewrite (ta_soff_denot _ 9 _ (EL 9%nat 9%bv eq_refl)); exact R9
          | rewrite (ta_soff_denot _ 18 _ (EL 18%nat 18%bv eq_refl)); exact R18
          | rewrite (ta_soff_denot _ 21 _ (EL 21%nat 21%bv eq_refl)); exact R21 ]
  end.

(* The run from a head to its call: the moves and the `jal`. It writes no memory, keeps every callee-saved register,
   and leaves ra = the return address and the argument registers. *)
Lemma ta_to_call : forall cx (W : world segs) regs mem md ly' S' k f pc ret callee args
    (Q : world segs -> config -> Prop),
  u_prem B MT XL RLO RHI -> In (pc, ret, callee, args) (ta_calls cx f) ->
  u_core B cx ly' S' W regs mem md [(f, u_fsz cx)] k -> u_fregs cx regs f ->
  (forall regs' md',
     u_core B cx ly' S' W regs' mem md' [(f, u_fsz cx)] k -> u_fregs cx regs' f ->
     YK11.getr regs' 1 = w64 (WIRE_A_LLVMF + ret) ->
     Forall (fun a => YK11.getr regs' (fst a) = w64 (snd a)) args ->
     SRr segs W (@cfg_at (u_fx cx) segs callee regs' mem md') Q) ->
  SRr segs W (u_cfg cx pc regs mem md) Q.
Proof.
intros cx W regs mem md ly' S' k f pc ret callee args Q HP Hin HC HFR HK.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm).
pose proof HFR as (R8 & R9 & R18 & R19 & R21 & R22).
pose proof (ta_seat (fx := u_fx cx) (rc := rc) pc W regs mem) as HS.
set (E0 := Eimg (PI := PI_wire) (Ereg regs [])) in HS.
assert (HEI : img_env (@pa_val _ wire_listing PI_wire) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ wire_listing PI_wire) (SOff 21 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (split; [intros nn Hnn; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
pose proof (paj_run (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUN.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr (@pa_segs _ wire_listing PI_wire) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + pc)) mem
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md) Qx) end.
cbn [ta_calls In] in Hin.
destruct Hin as [Hin | [Hin | [Hin | [Hin | [Hin | [Hin | [Hin | []]]]]]]];
  injection Hin as E1 E2 E3 E4; subst pc ret callee args.
all: paj_run_tok RUN HS HJ SHOK Bspan; [ta_awr_ro|].
all: ta_md mdA.
all: apply frame_of_read_only in HF; [|vm_compute; reflexivity].
all: rename HF into Hm; clear HFr HG.
all: lazymatch type of HS with st_ok _ _ ?ss _ =>
  pose proof (regs_kept_of_st_ok (@pa_segs _ wire_listing PI_wire) E0 ss (restrict (w_H W) ms) regs []
    [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KA end.
all: cbn [ms_regs restrict] in KA.
all: ta_reg HS (1%bv : bv 5) R1'; cbn [ms_regs restrict] in R1'.
all: pmkst HS; rewrite Hm in HJ |- *.
all: apply (HK (ms_regs ms) mdA).
all: first
  [ refine (conj HJ (conj Hfrs (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hsv Hperm)))))))))));
    [ unfold spZ in *; rewrite (KA 2%bv ltac:(ta_in)); exact Hsp
    | rewrite (KA 3%bv ltac:(ta_in)); exact Hgp
    | rewrite (KA 4%bv ltac:(ta_in)); exact Htp
    | rewrite (KA 23%bv ltac:(ta_in)); exact H23
    | rewrite (KA 24%bv ltac:(ta_in)); exact H24
    | rewrite (KA 25%bv ltac:(ta_in)); exact H25
    | rewrite (KA 26%bv ltac:(ta_in)); exact H26
    | rewrite (KA 27%bv ltac:(ta_in)); exact H27 ]
  | unfold u_fregs;
    rewrite (KA 8%bv ltac:(ta_in)), (KA 9%bv ltac:(ta_in)), (KA 18%bv ltac:(ta_in)), (KA 19%bv ltac:(ta_in)),
      (KA 21%bv ltac:(ta_in)), (KA 22%bv ltac:(ta_in));
    exact (conj R8 (conj R9 (conj R18 (conj R19 (conj R21 R22)))))
  | rewrite R1'; exact (codeptr_val E0 _ HEI)
  | repeat (apply Forall_cons; [cbn [fst snd]; ta_arg HS EL R8 R9 R18 R21|]); apply Forall_nil ].
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The segment                                                       *)
(* ------------------------------------------------------------------ *)

(* One stretch and its call (row i of ta_calls): from ta_st at a head to ta_st at the return address. *)
Ltac ta_leg HP HB cx Hst i lem :=
  let Hin := fresh "Hin" in
  destruct Hst as (ly' & S' & regs & mem & md & f & -> & Hn & HC & HM & HFR & Hg);
  pose proof (@nth_error_In _ (ta_calls cx f) i _ eq_refl) as Hin;
  eapply (ta_to_call _ _ regs mem md ly' S' _ f _ _ _ _ _ HP Hin HC HFR);
  intros regs' md' HC' HFR' R1 Hargs;
  repeat (let Ha := fresh "Ha" in apply Forall_cons_iff in Hargs as [Ha Hargs]; cbn [fst snd] in Ha);
  eapply lem; first [eassumption | exact HP | exact HB | exact Hn |
    unfold U_EV_PRE, U_EV_OH, PFWD.CF_EV, PRET.CR_EV, PDS.CDS_EV, PMET.CM_EV, PCNT.CK_EV, PWID.CW_EV, PRD.CRD_EV;
    lia].

Theorem u_turn_a_ok : u_turn_a_stmt B MT XL RLO RHI.
Proof.
intros HP cx W c HB HOH.
change (ta_st cx U_OH U_EV_OH W c) in HOH.
change (SRr segs W c (ta_st cx U_PRE U_EV_PRE)).
eapply SRr_bind; [ta_leg HP HB cx HOH 0%nat ta_cfwd|]. intros W1 c1 _ H1.
eapply SRr_bind; [ta_leg HP HB cx H1 1%nat ta_cret|]. intros W2 c2 _ H2.
eapply SRr_bind; [ta_leg HP HB cx H2 2%nat ta_cds|]. intros W3 c3 _ H3.
eapply SRr_bind; [ta_leg HP HB cx H3 3%nat ta_cmet|]. intros W4 c4 _ H4.
eapply SRr_bind; [ta_leg HP HB cx H4 4%nat ta_ccnt|]. intros W5 c5 _ H5.
eapply SRr_bind; [ta_leg HP HB cx H5 5%nat ta_cwid|]. intros W6 c6 _ H6.
ta_leg HP HB cx H6 6%nat ta_crd.
Qed.
End ta.
