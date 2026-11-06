(* Modified by Theorem Labs, 2026-10: in the form of projects/reac-repacer/fuzz_wire/proofs/lib/B/Prog/LLVMFuzzerTestOneInput_seg_exit.v (f610b082953b) for reac-repacer/fuzz_wire's image A: the image modules of lib/A, the offsets of fuzz_wire.asan, the free return addresses of WIRE_LLVMF_RA_FREE, and the cost of the image-A statement (u_cost_ladder, which charges the blocks at their size). *)
(* LLVMFuzzerTestOneInput_seg_exit: u_exit_ok : u_exit_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the exit of
   the image-A walk of fuzz_wire.asan's LLVMFuzzerTestOneInput: runs of the Pa engine to a call, the free rule at the
   call, the run from its return address, and the teardown (the reloads, the return and the slot post out of the
   journal).

   Three runs of the Pa engine, each from a seat with the registers as atoms (Ereg regs extra):
   - +0x144 .. +0x148 and +0x14c .. +0x150 (no region): `mv a0, s3` (c) or `mv a0, s0` (f), then the `jal` to the
     free trampoline (0x522f4) with ra = +0x14c or +0x154; ux_free takes the call by u_prem's free rule
     (lib/Reusable/YC5d.v afree04_rule): the block is one of this call's own (the blocks are pairwise disjoint, so it
     is not one of the caller's), the frame-pointer chain is empty (s0 = f lies below sp), and the trace is one of
     wire_llvmf_ufix's;
   - +0x154 .. +0x17c: one read-only region on sp holding the eight saved words (extra atoms 32 .. 39, the caller's
     registers in wire_saved_at's order); a0 = 0, the eight reloads, sp += 0x40; the return at +0x17c goes to the
     caller's ra = RA_LLVMF, and the slot post (u_post) comes out of the journal (its FP = [] journal read at the
     sink token's FP by t_fp_token). The refusal reaches +0x154 directly (u_st_ret).
   The two frees cost what u_cost_ladder adds to U_C_C (u_st_exit carries 0 < size, and the slot pre bounds it). *)
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
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaJournal WirePSyms WirePList WirePAddr
  WirePPa WirePPaLib WirePImg WirePPaImg WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* 1. Values, registers, blocks                                        *)
(* ------------------------------------------------------------------ *)

Lemma ux_soff_denot : forall E (a : nat) w, ew E a = w -> sv_denot E (SOff a 0) = w.
Proof. intros E a w Ha. cbn [sv_denot]. rewrite Ha, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* The registers a run to a free call and the call itself keep: sp, gp, tp and the callee-saved s0 .. s11. *)
Definition ux_kept : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* A callee-saved register through aregs_preserved. *)
Lemma ux_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr regs2 r = YK11.getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac ux_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let x := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with x; unfold acallee_saved; lia end.
Ltac ux_in := try unfold ux_kept; cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).

Lemma ux_kept_cs : forall r, In r ux_kept -> acallee_saved (bv_unsigned r).
Proof. intros r Hr. unfold ux_kept in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [ux_cs|]). destruct Hr. Qed.

(* The allocator's trace at a call with an empty chain (YCbq.v call_trace0) is WireCg.v's wire_utrace of the
   return address. *)
Lemma ux_trace0 : forall pc0 regs, call_trace0 pc0 regs [] = wire_utrace pc0 [raZ regs].
Proof.
intros pc0 regs. rewrite call_trace_nil. unfold wire_utrace. cbn [flat_map].
destruct (raZ regs =? pc0); reflexivity.
Qed.

(* A frame pointer at or below sp ends the chain (YG00.v bad_next). *)
Lemma ux_chain_nil : forall ly rd (regsT : bvmap 5 word),
  4096 <= raZ regsT -> s0Z regsT <= spZ regsT -> chain_pre ly rd regsT [].
Proof.
intros ly rd regsT Hra Hs. unfold chain_pre. split; [exact Hra|].
destruct (frame0_ok ly regsT); [|reflexivity].
unfold bad_next. rewrite (proj2 (Z.leb_le _ _) Hs). reflexivity.
Qed.

(* Pairwise disjoint blocks of size >= 1 are distinct. *)
Lemma ux_nodup : forall l : list (Z * Z),
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> Forall (fun b => 0 <= snd b) l -> List.NoDup l.
Proof.
induction l as [|b l IH]; intros Hp Hn; [apply List.NoDup_nil|].
cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. apply Forall_cons_iff in Hn as [Hb Hn].
apply List.NoDup_cons; [|exact (IH Hp Hn)].
intros Hin. apply (proj1 (Forall_map _ _ _)) in Hf.
pose proof (proj1 (Forall_forall _ _) Hf b Hin) as Hd. cbn beta in Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (snd b) Hb) as [H1 _]. lia.
Qed.
Lemma ux_nodup_app_not_in : forall (L M : list (Z * Z)) a, List.NoDup (L ++ M) -> In a M -> ~ In a L.
Proof.
induction L as [|b L IH]; intros M a Hnd Hm Hl; [destruct Hl|].
cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hb Hnd].
destruct Hl as [<- | Hl].
- apply Hb. apply in_or_app. right. exact Hm.
- exact (IH M a Hnd Hm Hl).
Qed.

(* The events of the whole call: one malloc and one free each for f and c, check_copy's malloc and free. *)
Lemma ux_ev_ret : U_EV_RET = 6.
Proof. reflexivity. Qed.

(* The return addresses of the two free calls (LLVMFuzzerTestOneInput_cg.v WIRE_LLVMF_RA_FREE), and their bounds. *)
Definition UX_RA_FREE1 : Z := WIRE_A_LLVMF + 0x14c.
Definition UX_RA_FREE2 : Z := WIRE_A_LLVMF + 0x154.
Lemma ux_ra_free_in : In UX_RA_FREE1 WIRE_LLVMF_RA_FREE /\ In UX_RA_FREE2 WIRE_LLVMF_RA_FREE.
Proof. unfold WIRE_LLVMF_RA_FREE. cbn [map In]. split; [left | right; left]; reflexivity. Qed.
Lemma ux_ra_free :
  (4096 <= UX_RA_FREE1 < 2 ^ 64 /\ UX_RA_FREE1 mod 2 = 0) /\
  (4096 <= UX_RA_FREE2 < 2 ^ 64 /\ UX_RA_FREE2 mod 2 = 0).
Proof. unfold UX_RA_FREE1, UX_RA_FREE2, WIRE_A_LLVMF, wire_text, AF_LLVMFuzzerTestOneInput. lia. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The seats                                                        *)
(* ------------------------------------------------------------------ *)

(* +0x144 / +0x14c: no region, no fact. *)
Definition ux_nofacts : facts := mkFacts [] [] [].
Definition ss_xc (pc : Z) : sstate := mkSS pc sr_atoms [] None ux_nofacts.

(* +0x154: the eight saved words of [sp1, sp1 + 0x40), read only (atoms 32 .. 39 in wire_saved_at's order). *)
Definition ux_sv : list YP09.chunk :=
  [YP09.mkChunk 0x38 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x30 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0x28 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x20 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0x18 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x10 (CVal 8 (SOff 37 0));
   YP09.mkChunk 0x8 (CVal 8 (SOff 38 0)); YP09.mkChunk 0x0 (CVal 8 (SOff 39 0))].
Definition ux_fr2 : YP09.region := YP09.mkRegion (Some 2%nat) 0 0x40 0 0 ux_sv.
Definition ux_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_x2 : sstate := mkSS U_RET sr_atoms [ux_fr2] None ux_facts.
Definition ux_ex2 (regs0 : bvmap 5 word) : list word :=
  map (fun o : Z * Z => YK11.getr regs0 (Z_to_bv 5 (snd o))) wire_saved_at.

Section seat. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ wire_listing PI_wire).
Local Abbreviation VAL := (@pa_val _ wire_listing PI_wire).
Local Abbreviation BASE := (@pa_val _ wire_listing PI_wire A_TEXT).

Lemma ux_seat_call : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (Eimg (PI := PI_wire) (Ereg regs [])) (ss_xc pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc.
rewrite restrict_mkst_fx. unfold ss_xc.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- exact (conj I (conj I I)).
Qed.

Lemma ux_seat_ret : forall (W : world SEGS) (regs regs0 : bvmap 5 word) mem sp0,
  spZ regs = sp0 - 0x40 -> 2 ^ 46 <= sp0 - 0x40 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  Forall (fun o : Z * Z => rdword (aview SEGS (w_H W) mem) (sp0 - fst o) =
    Some (bv_unsigned (YK11.getr regs0 (Z_to_bv 5 (snd o))))) wire_saved_at ->
  st_ok_pi SEGS VAL (Eimg (PI := PI_wire) (Ereg regs (ux_ex2 regs0))) ss_x2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + U_RET)) mem (seg_rom SEGS))).
Proof.
intros W regs regs0 mem sp0 Hsp Hlo Hhi H16 Hsv.
rewrite restrict_mkst_fx. unfold ss_x2.
set (E := Eimg (PI := PI_wire) (Ereg regs (ux_ex2 regs0))).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 0x40)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (ux_ex2 regs0) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
unfold wire_saved_at in Hsv. cbn [fst snd] in Hsv.
repeat match type of Hsv with Forall _ (_ :: _) =>
  apply Forall_cons_iff in Hsv; let H := fresh "Hw" in destruct Hsv as [H Hsv]; cbn [fst snd] in H end.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, ux_fr2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold ux_sv.
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
    let j := eval vm_compute in (n - 32)%nat in
    let o := eval vm_compute in (0x40 - off) in
    lazymatch goal with Hw : rdword _ (sp0 - o) = Some ?v |- _ =>
      apply (chunk_ok_val SEGS E _ (sp0 - 0x40) off 8 (SOff n 0) v);
      [ cbn [sv_denot]; let Ej := fresh "Ej" in pose proof (EX j ltac:(lia)) as Ej; cbn [Nat.add] in Ej; rewrite Ej;
        cbn [nth ux_ex2 map wire_saved_at snd];
        rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 8) with 64; apply bv_unsigned_in_range
      | cbn; lia
      | replace (sp0 - 0x40 + off) with (sp0 - o) by lia; exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hw) ]
    end
  end.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [ux_facts f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16. lia.
Qed.
End seat.

(* ------------------------------------------------------------------ *)
(* 3. Tactics of the runs                                              *)
(* ------------------------------------------------------------------ *)

(* A register's symbolic value at a state (st_ok_pi, or st_ok at a call). *)
Ltac ux_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok ?sg ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
(* The write rights of a run with read-only regions only. *)
Ltac ux_awr_ro :=
  lazymatch goal with |- awr_ok ?Ey ?rsx ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ey rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ].
(* The model after a run, named. *)
Ltac ux_md md2 :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) in *; clearbody md2 end.

(* ------------------------------------------------------------------ *)
(* 4. The frame and the free call                                      *)
(* ------------------------------------------------------------------ *)

Section sg. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc AE2k.tfib_sink_head segs B).

(* The stack facts of the journal: the entry sp's alignment and bounds, the stack window present, and the layout's
   stack range around it. *)
Lemma ux_J_facts : forall cx ly' S' W mem md k,
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem md k ->
  u_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= u_sp0 cx /\ u_sp0 cx <= 2 ^ 47 /\
  (forall a, u_sp0 cx - LLVMF_STK <= a < u_sp0 cx -> apresent (w_H W) mem a) /\
  ly_stk_lo (u_ly cx) + LLVMF_STK <= u_sp0 cx /\ u_sp0 cx <= ly_stk_hi (u_ly cx) /\ alloc_ceiling <= ly_stk_lo (u_ly cx).
Proof.
intros cx ly' S' W mem md k HJ.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (H16 & _ & Hceil & Hlo & Hhi & H47 & _).
refine (conj H16 (conj _ (conj _ (conj Hpres (conj Hlo (conj Hhi Hceil)))))); lia.
Qed.

(* The saved words lie in [sp0 - 64, sp0): a view that keeps those bytes keeps them. *)
Lemma ux_saved_kept : forall cx (r r' : reader), u_saved cx r ->
  (forall a, u_sp0 cx - 64 <= a < u_sp0 cx -> r' a = r a) -> u_saved cx r'.
Proof.
intros cx r r' Hs Hk. unfold u_saved in *. rewrite Forall_forall in *. intros o Ho.
rewrite <- (Hs o Ho). apply rdword_kept. intros k Hk8.
assert (Hf : 8 <= fst o <= 64).
{ unfold wire_saved_at in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply Hk. lia.
Qed.

(* A run that kept sp, gp, tp, s7 .. s11 and the saved words keeps the frame invariant. *)
Lemma ux_core_kept : forall cx ly' S' (W : world segs) regs regs' mem mem' md md' bl k,
  u_core B cx ly' S' W regs mem md bl k ->
  ajournal LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly' S' W mem' md' k ->
  (forall r : bv 5, In r ux_kept -> YK11.getr regs' r = YK11.getr regs r) ->
  (forall a, u_sp0 cx - 64 <= a < u_sp0 cx -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  u_core B cx ly' S' W regs' mem' md' bl k.
Proof.
intros cx ly' S' W regs regs' mem mem' md md' bl k
  (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm) HJ' KA KV.
refine (conj HJ' (conj Hfrs (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ Hperm))))))))))).
- unfold spZ in *. rewrite (KA 2%bv ltac:(ux_in)). exact Hsp.
- rewrite (KA 3%bv ltac:(ux_in)). exact Hgp.
- rewrite (KA 4%bv ltac:(ux_in)). exact Htp.
- rewrite (KA 23%bv ltac:(ux_in)). exact H23.
- rewrite (KA 24%bv ltac:(ux_in)). exact H24.
- rewrite (KA 25%bv ltac:(ux_in)). exact H25.
- rewrite (KA 26%bv ltac:(ux_in)). exact H26.
- rewrite (KA 27%bv ltac:(ux_in)). exact H27.
- exact (ux_saved_kept cx _ _ Hsv KV).
Qed.

(* s0 holds one of this call's live blocks, which lies below the stack. *)
Lemma ux_s0_le : forall cx ly' S' (W : world segs) regs mem md bl k f,
  u_prem B MT XL RLO RHI -> u_core B cx ly' S' W regs mem md bl k -> In (f, u_fsz cx) bl ->
  YK11.getr regs 8 = w64 f -> s0Z regs <= spZ regs.
Proof.
intros cx ly' S' W regs mem md bl k f HP HC Hin R8.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & _ & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & Hperm).
pose proof HJ as (HAR & _).
destruct (ux_J_facts cx _ _ _ _ _ _ HJ) as (_ & Hceil & H47 & _).
assert (Hin' : In (f, u_fsz cx) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin') as (_ & Hf4 & Hfc & _).
pose proof (req_size_pos (u_fsz cx) ltac:(unfold u_fsz; lia)) as [Hr _].
assert (Hf : s0Z regs = f) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
rewrite Hf, Hsp. unfold u_sp1, U_FRAME, LLVMF_STK in *. lia.
Qed.

(* free (x) at the trampoline by u_prem's free rule, x one of this call's blocks: the frame invariant at the block's
   removal and one more event, the meter one free more, the callee-saved registers kept. *)
Lemma ux_free : forall cx (W : world segs) regsT memT mdT ly' S' (bl1 bl2 : list (Z * Z)) x k c ra
    (Q : world segs -> config -> Prop),
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  u_core B cx ly' S' W regsT memT mdT (bl1 ++ (x, u_fsz cx) :: bl2) k -> k + 1 <= U_EV_RET ->
  u_meter MT XL cx S' c -> c + mo_free MT <= wire_llvmf_cost MT (u_n cx) ->
  In (wire_utrace (pc_free_ra0 (as_code B)) [ra]) (as_universe B) ->
  4096 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  YK11.getr regsT 1 = w64 ra -> YK11.getr regsT 10 = w64 x -> s0Z regsT <= spZ regsT ->
  (forall W2 ly2 S2 regs2 mem2 md2, wle W W2 ->
     u_core B cx ly2 S2 W2 regs2 mem2 md2 (bl1 ++ bl2) (k + 1) ->
     u_meter MT XL cx S2 (c + mo_free MT) ->
     (forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regsT r) ->
     SRr segs W2 (mkCfg (@YK11.mkst (u_fx cx) regs2 (w64 ra) mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (@cfg_at (u_fx cx) segs (wire_sigma WS___interceptor_trampoline_free) regsT memT mdT) Q.
Proof.
intros cx W regsT memT mdT ly' S' bl1 bl2 x k c ra Q HP HB HC Hk (Hle & Hmo) Hc HTR Hra Hra2 R1 R10 Hs0 HK.
pose proof (up_laws _ _ _ _ _ HP) as LAWS. pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm).
pose proof HB as HB'. unfold u_base, tfib_lib_pre_x in HB'.
destruct HB' as (_ & _ & _ & _ & Hpn & _ & _ & _ & Hnev & _).
assert (Hn0 : 0 <= u_n cx) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
pose proof (up_cost _ _ _ _ _ HP (u_n cx) Hn0) as HXL.
destruct (ux_J_facts cx _ _ _ _ _ _ HJ) as (H16 & Hceil & H47 & _).
pose proof alloc_ceiling_val as Hce.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev' & _).
assert (Hin : In (x, u_fsz cx) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
assert (Hnot : ~ In (x, u_fsz cx) (ablocks B (u_ly cx) (u_S cx))).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
  assert (Hnn : Forall (fun b => 0 <= snd b) (ablocks B ly' S')).
  { apply Forall_forall. intros [p q] Hpq.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpq) as (_ & _ & _ & _ & _ & _ & Hq). cbn [snd]. lia. }
  assert (Hnd : List.NoDup (ablocks B (u_ly cx) (u_S cx) ++ bl1 ++ (x, u_fsz cx) :: bl2))
    by (eapply Permutation_NoDup; [exact Hperm | exact (ux_nodup _ Hpw Hnn)]).
  apply (ux_nodup_app_not_in _ _ _ Hnd). apply in_or_app. right. left. reflexivity. }
assert (Hraz : raZ regsT = ra) by (unfold raZ; rewrite R1; apply unsigned_lit_small; lia).
assert (MOK : mo_ok MT S' (mo_free MT)) by (apply (mo_ok_le MT ML S' _ _ Hmo); lia).
assert (TRACE : In (call_trace0 (pc_free_ra0 (as_code B)) regsT []) (as_universe B))
  by (rewrite ux_trace0, Hraz; exact HTR).
assert (CHAIN : chain_pre ly' (aview segs (w_H W) memT) regsT [])
  by (apply ux_chain_nil; [rewrite Hraz; lia | exact Hs0]).
assert (Hw : bv_unsigned (w64 ra) = ra) by (apply unsigned_lit_small; lia).
assert (RET : YK0s.ret_ok (w64 ra)) by (apply YK0s.ret_ok_even; rewrite Hw; exact Hra2).
assert (NEV : st_nev S' < EV_MAX) by (pose proof ux_ev_ret; unfold EV_LIB in *; lia).
unfold cfg_at. rewrite <- (up_wrap_free _ _ _ _ _ HP).
eapply SRr_bind.
{ exact (up_free _ _ _ _ _ HP (u_fx cx) W regsT memT LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx)
    (u_md cx) [] ly' S' mdT k x (u_fsz cx) (-64) (w64 ra) [] HJ Hin R10
    ltac:(rewrite Hsp; unfold u_sp1, U_FRAME; lia) eq_refl ltac:(lia) ltac:(unfold ASTACK, LLVMF_STK; lia)
    Hgp Htp R1 RET NEV CHAIN TRACE (fun H => False_ind _ (Hnot H)) MOK). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPr & (l1 & l2 & E1 & E2) & Hfr2 & HKp & Hmle).
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regsT r)
  by (intros r Hr; exact (ux_pres regsT regs2 r HPr Hr)).
apply (HK W2 ly2 S2 regs2 mem2 md2 Hwle); [| |exact P].
- destruct HKp as (K1 & _).
  refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
  + rewrite Hfr2. exact Hfrs.
  + unfold spZ in *. rewrite (P 2%bv ltac:(ux_cs)). exact Hsp.
  + rewrite (P 3%bv ltac:(ux_cs)). exact Hgp.
  + rewrite (P 4%bv ltac:(ux_cs)). exact Htp.
  + rewrite (P 23%bv ltac:(ux_cs)). exact H23.
  + rewrite (P 24%bv ltac:(ux_cs)). exact H24.
  + rewrite (P 25%bv ltac:(ux_cs)). exact H25.
  + rewrite (P 26%bv ltac:(ux_cs)). exact H26.
  + rewrite (P 27%bv ltac:(ux_cs)). exact H27.
  + apply (ux_saved_kept cx _ _ Hsv). intros a Ha. apply K1; unfold u_sp1, U_FRAME, ASTACK, LLVMF_STK in *; lia.
  + rewrite E2. rewrite E1 in Hperm. rewrite app_assoc in Hperm |- *. eapply Permutation_app_inv. exact Hperm.
- split.
  + exact (mo_le_trans MT ML _ _ _ _ _ Hle Hmle).
  + apply (mo_ok_step MT ML S' S2 (mo_free MT)); [|exact Hmle].
    replace (mo_free MT + (XL (u_n cx) - (c + mo_free MT))) with (XL (u_n cx) - c) by lia. exact Hmo.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The runs                                                         *)
(* ------------------------------------------------------------------ *)

(* From +0x144 (`mv a0, s3`) or +0x14c (`mv a0, s0`) to the `jal` of the free trampoline, then the free. The run
   writes no byte (no region) and only a0 and ra. *)
Lemma ux_call_free1 : forall cx (W : world segs) regs mem md ly' S' bl1 bl2 x k c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  u_core B cx ly' S' W regs mem md (bl1 ++ (x, u_fsz cx) :: bl2) k -> k + 1 <= U_EV_RET ->
  u_meter MT XL cx S' c -> c + mo_free MT <= wire_llvmf_cost MT (u_n cx) ->
  YK11.getr regs 19 = w64 x -> s0Z regs <= spZ regs ->
  forall Q : world segs -> config -> Prop,
  (forall W2 ly2 S2 regs2 mem2 md2, wle W W2 ->
     u_core B cx ly2 S2 W2 regs2 mem2 md2 (bl1 ++ bl2) (k + 1) -> u_meter MT XL cx S2 (c + mo_free MT) ->
     (forall r : bv 5, In r ux_kept -> YK11.getr regs2 r = YK11.getr regs r) ->
     SRr segs W2 (u_cfg cx 0x14c regs2 mem2 md2) Q) ->
  SRr segs W (u_cfg cx U_EXIT regs mem md) Q.
Proof.
intros cx W regs mem md ly' S' bl1 bl2 x k c HP HB HC Hk HM Hc Hrs Hs0 Q HK.
pose proof (up_ufix _ _ _ _ _ HP) as HU. unfold wire_llvmf_ufix in HU. destruct HU as (_ & HU).
pose proof (HU UX_RA_FREE1 (proj1 ux_ra_free_in)) as HTR.
set (ra := UX_RA_FREE1) in HTR.
destruct (proj1 ux_ra_free) as (Hra & Hra2). fold ra in Hra, Hra2.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & _).
pose proof (@ux_seat_call (u_fx cx) rc W regs mem U_EXIT) as HS.
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
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + U_EXIT)) mem
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md) Qx) end.
paj_run_tok RUN HS HJ SHOK Bspan; [ux_awr_ro|].
ux_md mdA.
assert (HM1 : forall y, ms_mem ms y = mem y)
  by (intros y; apply HF; intros (rg & Hrg & _); cbn in Hrg; destruct Hrg).
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx _ =>
  pose proof (regs_kept_of_st_ok (@pa_segs _ wire_listing PI_wire) E0 ssx (restrict (w_H W) ms) regs []
    ux_kept HS HAE ltac:(vm_compute; reflexivity)) as KA end.
cbn [ms_regs restrict] in KA.
ux_reg HS (1%bv : bv 5) R1'. ux_reg HS (10%bv : bv 5) R10'.
cbn [ms_regs restrict] in R1', R10'.
assert (R1 : YK11.getr (ms_regs ms) 1 = w64 ra) by (rewrite R1'; exact (codeptr_val E0 _ HEI)).
assert (R10 : YK11.getr (ms_regs ms) 10 = w64 x)
  by (rewrite R10', (ux_soff_denot E0 19 _ (EL 19%nat 19%bv eq_refl)); exact Hrs).
pmkst HS.
apply (ux_free cx W (ms_regs ms) (ms_mem ms) mdA ly' S' bl1 bl2 x k c ra Q HP HB).
- apply (ux_core_kept cx ly' S' W regs (ms_regs ms) mem (ms_mem ms) md mdA _ k HC HJ KA).
  intros a Ha. apply (aview_eq_of segs). unfold mrestrict. rewrite (HM1 (Z_to_bv 64 a)). reflexivity.
- exact Hk.
- exact HM.
- exact Hc.
- exact HTR.
- exact Hra.
- exact Hra2.
- exact R1.
- exact R10.
- unfold s0Z, spZ. rewrite (KA 8%bv ltac:(ux_in)), (KA 2%bv ltac:(ux_in)). exact Hs0.
- intros W2 ly2 S2 regs2 mem2 md2 Hwle HC2 HM2 HP2. apply (HK W2 ly2 S2 regs2 mem2 md2 Hwle HC2 HM2).
  intros r Hr. rewrite (HP2 r (ux_kept_cs r Hr)). exact (KA r Hr).
Qed.

Lemma ux_call_free2 : forall cx (W : world segs) regs mem md ly' S' bl1 bl2 x k c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx ->
  u_core B cx ly' S' W regs mem md (bl1 ++ (x, u_fsz cx) :: bl2) k -> k + 1 <= U_EV_RET ->
  u_meter MT XL cx S' c -> c + mo_free MT <= wire_llvmf_cost MT (u_n cx) ->
  YK11.getr regs 8 = w64 x -> s0Z regs <= spZ regs ->
  forall Q : world segs -> config -> Prop,
  (forall W2 ly2 S2 regs2 mem2 md2, wle W W2 ->
     u_core B cx ly2 S2 W2 regs2 mem2 md2 (bl1 ++ bl2) (k + 1) -> u_meter MT XL cx S2 (c + mo_free MT) ->
     (forall r : bv 5, In r ux_kept -> YK11.getr regs2 r = YK11.getr regs r) ->
     SRr segs W2 (u_cfg cx U_RET regs2 mem2 md2) Q) ->
  SRr segs W (u_cfg cx 0x14c regs mem md) Q.
Proof.
intros cx W regs mem md ly' S' bl1 bl2 x k c HP HB HC Hk HM Hc Hrs Hs0 Q HK.
pose proof (up_ufix _ _ _ _ _ HP) as HU. unfold wire_llvmf_ufix in HU. destruct HU as (_ & HU).
pose proof (HU UX_RA_FREE2 (proj2 ux_ra_free_in)) as HTR.
set (ra := UX_RA_FREE2) in HTR.
destruct (proj2 ux_ra_free) as (Hra & Hra2). fold ra in Hra, Hra2.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & _).
pose proof (@ux_seat_call (u_fx cx) rc W regs mem 0x14c) as HS.
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
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + 0x14c)) mem
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md) Qx) end.
paj_run_tok RUN HS HJ SHOK Bspan; [ux_awr_ro|].
ux_md mdA.
assert (HM1 : forall y, ms_mem ms y = mem y)
  by (intros y; apply HF; intros (rg & Hrg & _); cbn in Hrg; destruct Hrg).
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx _ =>
  pose proof (regs_kept_of_st_ok (@pa_segs _ wire_listing PI_wire) E0 ssx (restrict (w_H W) ms) regs []
    ux_kept HS HAE ltac:(vm_compute; reflexivity)) as KA end.
cbn [ms_regs restrict] in KA.
ux_reg HS (1%bv : bv 5) R1'. ux_reg HS (10%bv : bv 5) R10'.
cbn [ms_regs restrict] in R1', R10'.
assert (R1 : YK11.getr (ms_regs ms) 1 = w64 ra) by (rewrite R1'; exact (codeptr_val E0 _ HEI)).
assert (R10 : YK11.getr (ms_regs ms) 10 = w64 x)
  by (rewrite R10', (ux_soff_denot E0 8 _ (EL 8%nat 8%bv eq_refl)); exact Hrs).
pmkst HS.
apply (ux_free cx W (ms_regs ms) (ms_mem ms) mdA ly' S' bl1 bl2 x k c ra Q HP HB).
- apply (ux_core_kept cx ly' S' W regs (ms_regs ms) mem (ms_mem ms) md mdA _ k HC HJ KA).
  intros a Ha. apply (aview_eq_of segs). unfold mrestrict. rewrite (HM1 (Z_to_bv 64 a)). reflexivity.
- exact Hk.
- exact HM.
- exact Hc.
- exact HTR.
- exact Hra.
- exact Hra2.
- exact R1.
- exact R10.
- unfold s0Z, spZ. rewrite (KA 8%bv ltac:(ux_in)), (KA 2%bv ltac:(ux_in)). exact Hs0.
- intros W2 ly2 S2 regs2 mem2 md2 Hwle HC2 HM2 HP2. apply (HK W2 ly2 S2 regs2 mem2 md2 Hwle HC2 HM2).
  intros r Hr. rewrite (HP2 r (ux_kept_cs r Hr)). exact (KA r Hr).
Qed.

(* The register r of the return state against the caller's: sp = atom 2 + 0x40 = sp0, gp / tp / s7 .. s11 kept by
   the frame invariant, ra and s0 .. s6 the saved words (atoms 32 .. 39). *)
Local Ltac ux_post_reg E0 EL EX U2 Hgp Htp H23 H24 H25 H26 H27 Hgp0 Htp0 :=
  lazymatch goal with
  | |- sv_denot _ (SOff 2 64) = _ =>
    cbn [sv_denot]; rewrite U2; unfold u_sp1, U_FRAME, u_sp0, spZ; rewrite Z.sub_add, Z_to_bv_bv_unsigned;
    first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 3 0) = _ =>
    rewrite (ux_soff_denot E0 3 _ (EL 3%nat 3%bv eq_refl)), Hgp, <- Hgp0;
    first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 4 0) = _ =>
    rewrite (ux_soff_denot E0 4 _ (EL 4%nat 4%bv eq_refl)), Htp, <- Htp0;
    first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 23 0) = _ =>
    rewrite (ux_soff_denot E0 23 _ (EL 23%nat 23%bv eq_refl)), H23; first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 24 0) = _ =>
    rewrite (ux_soff_denot E0 24 _ (EL 24%nat 24%bv eq_refl)), H24; first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 25 0) = _ =>
    rewrite (ux_soff_denot E0 25 _ (EL 25%nat 25%bv eq_refl)), H25; first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 26 0) = _ =>
    rewrite (ux_soff_denot E0 26 _ (EL 26%nat 26%bv eq_refl)), H26; first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff 27 0) = _ =>
    rewrite (ux_soff_denot E0 27 _ (EL 27%nat 27%bv eq_refl)), H27; first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | |- sv_denot _ (SOff ?n 0) = _ =>
    let j := eval vm_compute in (n - 32)%nat in
    let Ej := fresh "Ej" in pose proof (EX j ltac:(lia)) as Ej;
    cbn [Nat.add nth ux_ex2 map wire_saved_at snd] in Ej; rewrite (ux_soff_denot E0 n _ Ej);
    first [reflexivity | f_equal; apply bv_eq; reflexivity]
  end.

(* +0x154 .. +0x17c: a0 = 0, the eight reloads, sp += 0x40, the return; the slot post out of the journal: the journal
   at the sink token's FP (t_fp_token), at most EV_LIB events, the callee-saved registers, a0 = 0, the blocks, the
   file descriptors and the file system kept (t_journal_io), the leaf LL 0 (m_fs md) [], the sink and the metadata
   kept (u_prem's up_sink_kept / up_meta_kept), the meter within XL size (the whole call's cost and up_cost), the
   input bytes kept (the journal's block clause). *)
Lemma ux_ret : forall cx (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> u_st_ret B MT XL cx W c -> SRr segs W c (u_post B MT XL cx).
Proof.
intros cx W c HP HB (ly' & S' & regs & mem & md & -> & HC & Hle & Hmo).
pose proof (up_laws _ _ _ _ _ HP) as LAWS. pose proof (up_meter_laws _ _ _ _ _ HP) as ML.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H23 & H24 & H25 & H26 & H27 & Hsv & Hperm).
destruct (ux_J_facts cx ly' S' W mem md _ HJ) as (H16 & Hceil & H47 & Hpres & _).
pose proof alloc_ceiling_val as Hce.
pose proof (@ux_seat_ret (u_fx cx) rc W regs (u_regs cx) mem (u_sp0 cx) Hsp
  ltac:(unfold LLVMF_STK in *; lia) H47 H16 Hsv) as HS.
set (E0 := Eimg (PI := PI_wire) (Ereg regs (ux_ex2 (u_regs cx)))) in HS.
assert (HEI : img_env (@pa_val _ wire_listing PI_wire) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ wire_listing PI_wire) (SOff 21 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
assert (EX : forall j, (j < 8)%nat -> ew E0 (32 + j) = nth j (ux_ex2 (u_regs cx)) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U2 : bv_unsigned (ew E0 2) = u_sp1 cx) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hsp).
pose proof (paj_run_to (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUNTO.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ wire_listing PI_wire) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + U_RET)) mem
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 380; [ux_awr_ro|].
ux_md mdB.
clear HF HFr HG.
eapply paj_ret_at; [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'.
unfold u_base, tfib_lib_pre_x in HB.
destruct HB as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs0 & Hnev & Hbb & Haro & Hsink & Hfd & Hfs & Hmeta
  & Hmo0).
pose proof HAFN as (HAR0 & Hret & Hra4 & Hgp0 & Htp0 & _).
ux_reg HS (1%bv : bv 5) R1'. cbn [ms_regs restrict] in R1'.
assert (E32 : ew E0 32 = YK11.getr (u_regs cx) (Z_to_bv 5 1)) by exact (EX 0%nat ltac:(lia)).
assert (R1 : YK11.getr (ms_regs ms) 1 = Z_to_bv 64 RA_LLVMF).
{ rewrite R1', (ux_soff_denot E0 32 _ E32), <- Hra. unfold raZ. rewrite Z_to_bv_bv_unsigned.
  first [reflexivity | f_equal; apply bv_eq; reflexivity]. }
pose proof (ajournal_materialize segs B LAWS wire_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ) as HJ3.
destruct (t_journal_io _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (Efd & Efs).
exists ly', S', (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdB) mat' mdB), U_EV_RET.
split.
{ unfold cfg_at. rewrite R1, v_jalr_lit_even by (unfold RA_LLVMF; lia). reflexivity. }
unfold tfib_lib_post_x.
refine (conj (t_fp_token _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) _).
split; [pose proof ux_ev_ret; unfold EV_LIB; lia|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hr' as [->|Hr']); try subst r;
  lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?rr) = _ =>
    let Hq := fresh "Hq" in ux_reg HS (Z_to_bv 5 rr) Hq; cbn [ms_regs restrict] in Hq; rewrite Hq end;
  ux_post_reg E0 EL EX U2 Hgp Htp H23 H24 H25 H26 H27 Hgp0 Htp0. }
split; [ux_reg HS (10%bv : bv 5) R10'; cbn [ms_regs restrict] in R10'; rewrite R10'; reflexivity|].
split; [rewrite app_nil_r in Hperm; exact Hperm|].
split; [intros fd; rewrite Efd; reflexivity|].
split; [cbn [YO09.ll_fs]; exact Efs|].
split; [reflexivity|]. split; [reflexivity|]. split; [cbn [YO09.ll_fs]; exact Hfs|].
split; [exact (up_sink_kept _ _ _ _ _ HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3
  ltac:(unfold YI16.sink_open_fp, YI16.in_fp; intros (? & [] & _)) Hsink)|].
split; [exact (up_meta_kept _ _ _ _ _ HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 Hmeta)|].
split.
{ apply (mo_le_mono MT ML _ _ _ _ Hle).
  assert (Hn0 : 0 <= u_n cx) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
  exact (up_cost _ _ _ _ _ HP (u_n cx) Hn0). }
intros i Hi. destruct Hpn as [(Hn0 & _) | (Hnpos & Hinp)]; [lia|].
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 (u_p cx) (u_n cx) i Hinp).
- rewrite app_nil_r in Hperm. exact (Permutation_in _ (Permutation_sym Hperm) Hinp).
- unfold req_size. destruct (Z.eqb_spec (u_n cx) 0); lia.
- intros (rg & [] & _).
Qed.

(* +0x144 .. +0x154: free (c), then free (f); the state at +0x154 is u_st_ret. The two frees and U_C_C are the whole
   call's cost (u_cost_ladder, at 0 < size < 2 ^ 26: u_st_exit and the slot pre). *)
Lemma ux_frees : forall cx (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> u_st_exit B MT XL cx W c -> SRr segs W c (u_post B MT XL cx).
Proof.
intros cx W c HP HB (ly' & S' & regs & mem & md & f & cb & -> & Hn0 & HC & HM & R8 & R19).
pose proof (up_meter_laws _ _ _ _ _ HP) as ML. pose proof (mo_free_nonneg MT ML) as Hfree.
assert (Hn : 0 < u_n cx < 2 ^ 26).
{ pose proof HB as HB'. unfold u_base, tfib_lib_pre_x in HB'. destruct HB' as (_ & _ & _ & _ & Hpn & _).
  destruct Hpn as [(Hz & _) | (Hn & _)]; lia. }
pose proof (u_cost_ladder MT cx Hn) as Hlad.
pose proof (ux_s0_le cx ly' S' W regs mem md _ _ f HP HC ltac:(left; reflexivity) R8) as Hs0.
apply (ux_call_free1 cx W regs mem md ly' S' [(f, u_fsz cx)] [] cb U_EV_EXIT (U_C_C MT cx) HP HB HC
  ltac:(unfold U_EV_RET; lia) HM ltac:(lia) R19 Hs0).
intros W2 ly2 S2 regs2 mem2 md2 Hwle HC2 HM2 KA2.
assert (R8' : YK11.getr regs2 8 = w64 f) by (rewrite (KA2 8%bv ltac:(ux_in)); exact R8).
pose proof (ux_s0_le cx ly2 S2 W2 regs2 mem2 md2 _ _ f HP HC2 ltac:(left; reflexivity) R8') as Hs0'.
apply (ux_call_free2 cx W2 regs2 mem2 md2 ly2 S2 [] [] f (U_EV_EXIT + 1) (U_C_C MT cx + mo_free MT) HP HB HC2
  ltac:(unfold U_EV_RET; lia) HM2 ltac:(lia) R8' Hs0').
intros W3 ly3 S3 regs3 mem3 md3 Hwle3 HC3 HM3 _.
apply (ux_ret cx W3 _ HP HB).
exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split.
- replace U_EV_RET with (U_EV_EXIT + 1 + 1) by (unfold U_EV_RET; lia). exact HC3.
- replace (wire_llvmf_cost MT (u_n cx)) with (U_C_C MT cx + mo_free MT + mo_free MT) by lia. exact HM3.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Theorem u_exit_ok : u_exit_stmt B MT XL RLO RHI.
Proof.
intros HP cx W c HB [HEX | HR].
- exact (ux_frees cx W c HP HB HEX).
- exact (ux_ret cx W c HP HB HR).
Qed.
End sg.
