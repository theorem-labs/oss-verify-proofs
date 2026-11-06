(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the kit of the entry segment of answer's ASan walk (plugin-hostd/fuzz_command,
   0x8a4c0 .. 0x8a61c): the walk tactics answer_s1.v does not carry (as sup_resp's walk carried them over from
   cgif lib/A/ACkc.v), the symbolic entry state and its seed (cgif's flushFrame seed, lib/A/ACj0.v, as sup_resp's
   sr_entry), and the recorder's representation carried over a step that keeps the recorder's bytes. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_e1.v, with its module paths and module names changed; 246 of its 370 lines of code are new or changed and 150 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, stage 1, part a: the walk tactics, the
   symbolic entry state and its seed lemma, and the lemmas the entry stage (sup_add_s1.v) uses at the record call.

   The walk tactics are the A walk's stage 1 (a working branch 87f17ee4716, lib/A/Prog/sup_add_s1.v, from
   arg_i's walk and cgif's lib/A/ACkc.v), over B's kit. The entry state is B's: the 128-byte frame below the entry
   sp, the shadow GOT word 0xa5f50 (A_OBJ 0) and the shadow-base cell (A_OBJ 12), and the frame-mode flag's GOT
   word 0xa5fa8 (A_OBJ 1) and its cell (PALibF), as sup_resp's B walk seeds it. B reads no recorder byte before the
   call of record() (0x8a534), so the state holds no g_rec region. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaNoChain PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts CmdRecAns.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


(* ---- the walk tactics (the A walk's stage 1, from arg_i_s1.v and cgif lib/A/ACkc.v) ---- *)
Definition s1_chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Ltac s1_rnHEI E := lazymatch goal with H : img_env _ _ E |- _ => H | _ => fail "s1_rnHEI: no img_env fact for" E end.
Ltac s1_hei_pose Eo kk ws :=
let Ho := s1_rnHEI Eo in let H := fresh "HEIh" in
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as H | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as H ].
Ltac s1_nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac s1_evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 32)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
Ltac s1_rebaseE HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv ];
rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 32)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 32 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by s1_nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by s1_nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.
Ltac s1_subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac s1_submem_to := repeat (first [apply submem_keep; [s1_subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac s1_rreg_by HS r v pf H :=
lazymatch type of HS with st_ok_pi _ ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg _ Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf) | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf) end.
Definition s1_trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (s1_chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint s1_trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some 2%nat => s1_trim_region r lo hi :: t
| _ => r :: s1_trim_stack t lo hi end end.
Ltac s1_norm_ssp HS := lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* awr_ok over a state's regions: read-only regions drop out; each writable window is shown in awr_byte by [tacw]
   on a goal  awr_byte ... a  with  b + wlo <= a < b + whi  as Ha *)
Ltac s1_awr AG tacw :=
lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc f0 ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply awr_ok_cons_gen; [reflexivity | s1_evalE AG |
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; tacw |] ].
(* awr_ok of a state that holds the side-stack frame (1, fpos) at F: the stack, the frame, the frame's shadow *)
Ltac s1_awr_f AG fpos F := s1_awr AG ltac:(unfold awr_byte; first
  [ left; lia
  | right; right; right; left; exists 1, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia]
  | right; right; right; left; exists 1, fpos; split; [left; reflexivity | right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16; unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; unfold SB in *; lia] ]).
(* after a symbolic run the model is  with_vm_backing (m_vm_lazy md) mat md  in the goal and the journal: name it *)
Ltac s1_md := lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ =>
lazymatch d with
| with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := d) in *; clearbody m
| _ => idtac end end.
Lemma s1_aval_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YO0f.le_byte, YG0f.le_byte.
apply Z.mod_mod. lia.
Qed.
Lemma s1_bvrange : forall (r : bv 5) (regs : bvmap 5 word), 0 <= bv_unsigned (getr regs r) < 2 ^ 64.
Proof. intros r regs. pose proof (bv_unsigned_in_range 64 (getr regs r)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.

(* ---- the entry state ---- *)
(* Atoms: the registers (0..31), the shadow base SB (32), the frame-mode flag's cell (33). Regions: the 128-byte
   frame, the shadow GOT word and cell, the flag's GOT word and cell. The stage makes no inline check: no shadow
   entry. *)
Definition s1_Bx : sv := SOff 32 0.
Definition s1_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition s1_SH : list shent := [].
Definition s1_regions0 : smem :=
[ stack_region 128; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition s1_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0x10000 0x606000 2) ].
Definition ss_s1 : sstate := mkSS AF_sup_add sr_atoms s1_regions0 None (mkFacts s1_atoms0 [] []).
Definition s1_extra (uar : Z) : list word := map (Z_to_bv 64) [SB; uar].

(* a byte of g_rec or of record.spill *)
Definition s1_rec (a : Z) : Prop := A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
Lemma s1_rec_PG : forall a, s1_rec a -> inFP cmd_PG a.
Proof.
intros a Ha. unfold s1_rec, REC_SIZE, SC_SIZE in Ha. unfold cmd_PG. rewrite !inFP_cons.
destruct Ha as [Ha | Ha]; [left; lia | right; left; lia].
Qed.
(* record()'s footprint lies in sup_add's: g_rec's ncalls, the slot (a call of the table or the spill), and in the
   spill arm the recorder's blocks *)
Lemma s1_recfp : forall R O a, inFP (rca_recFP R O) a ->
inFP (sa_FP O) a /\ (inFP cmd_PG a \/ inFP (ablocks_fp O) a).
Proof.
intros R O a H. unfold rca_recFP, rec_slot in H. unfold sa_FP, cmd_PG. rewrite !inFP_cons.
revert H. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt; intros H; cbv beta iota in H; rewrite !inFP_cons in H.
- apply PeanoNat.Nat.ltb_lt in Elt.
  unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, CALL_SIZE, SC_SIZE in *.
  destruct H as [H | [H | H]].
  + split; [left; lia | left; left; lia].
  + split; [right; left; lia | left; left; lia].
  + destruct (inFP_nil a H).
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, CALL_SIZE, SC_SIZE in *.
  destruct H as [H | [H | H]].
  + split; [left; lia | left; left; lia].
  + split; [right; right; right; left; lia | left; right; left; lia].
  + split; [right; right; right; right; exact H | right; exact H].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.

(* the entry state: B's frame of 128 bytes, the shadow GOT word and cell, the frame-mode flag's GOT word and cell
   (the record's constant cell holds 1, so `beqz` at 0x8a470 falls through) *)
Lemma s1_entry : forall W ly S regs mem md ch,
afn_pre SEGS B SUP_ADD_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (s1_extra (as_uar_cell B)))) ss_s1
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_add)) mem (seg_rom SEGS))).
Proof using LAWS TL TLF.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : 128 <= SUP_ADD_STK) by (unfold SUP_ADD_STK, ESTACK; lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (s1_extra (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_s1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s1_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
  [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 33%nat (as_uar_cell B) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold s1_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob1 Hob12 Huar Hsep. clear.
unfold ASAN_CEIL. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok s1_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33.
rewrite !unsigned_lit_small by (unfold SB in *; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
Qed.

(* the 13 saves of the real frame (ra s0 s1 .. s11 at sp0 - 8 .. sp0 - 104, 0x8a408-0x8a438), from the stack
   region of a symbolic state *)
Lemma s1_frame_of_region : forall E (W : world SEGS) (m : word -> option byte) sp0 (regs : bvmap 5 word) wlo whi,
region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) (-104) 0 wlo whi
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
sa_frame (aview SEGS (w_H W) m) sp0 regs.
Proof.
intros E W m sp0 regs wlo whi HR Hsp HE j r Hj.
apply s1_aval_of_val_mem.
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some sa_saved j)); rewrite Hj; discriminate).
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
do 13 (destruct j as [|j];
[ cbn in Hj; injection Hj as <-;
  lazymatch goal with |- val_mem _ _ (_ + ?od) _ (bv_unsigned (getr _ (Z_to_bv 5 ?R))) =>
  let od' := eval vm_compute in od in change od with od';
  let nn := eval vm_compute in (Z.to_nat R) in
  apply (field_of_region E _ 2 sp0 _ (-104) 0 wlo whi od' 8 (SOff nn 0) _ HR Hsp);
  [ cbn; tauto
  | cbn [sv_denot]; rewrite (HE nn (Z_to_bv 5 R) eq_refl), Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
  | exact HRr
  | cbn; lia ] end
| ]). cbn in Hj13. lia.
Qed.

(* the recorder's blocks are live blocks *)
Lemma s1_O_blocks : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HQ & HO) pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HQ pn (proj1 (HO pn) Hpn)). Qed.
(* the recorder's representation after steps that keep g_rec, record.spill and the bytes of its blocks *)
Lemma s1_rep_kept : forall ly S rd ly' S' (rd' : reader) R O,
rec_repA B ly S rd R O -> (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, s1_rec a -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < req_size n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O HREP HOb KR KB. apply (rec_repA_kept B ly S rd ly' S' rd' R O HREP HOb).
intros a [Ha | [Ha | Ha]]; [apply KR; left; exact Ha | apply KR; right; exact Ha|].
destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hpn & Hr).
replace a with (p + (a - p)) by lia. apply (KB p n); [exact Hpn | lia].
Qed.
(* sup_add's footprint holds the program's statics and the recorder's blocks (CmdRecRest's cmd_rodata_kept) *)
Lemma s1_saFP_cases : forall ly S rd ly' S' R O, rec_repA B ly S rd R O ->
forall a, inFP (sa_FP O) a -> Exists (in_zr a) TFIB_PROG_STATIC \/
  exists b n, In (b, n) (ablocks B ly S ++ ablocks B ly' S') /\ b <= a < b + req_size n.
Proof.
intros ly S rd ly' S' R O HREP a Ha. unfold sa_FP in Ha. rewrite !inFP_cons in Ha.
destruct Ha as [H | [H | [H | [H | H]]]];
[ left; apply Exists_cons_hd; unfold in_zr, A_G_REC, OFF_NCALLS in *; cbn [fst snd]; lia
| left; apply Exists_cons_hd; unfold in_zr, A_G_REC, OFF_CALLS, OFF_ANSWER in *; cbn [fst snd]; lia
| left; apply Exists_cons_hd; unfold in_zr, A_G_REC, OFF_STATE in *; cbn [fst snd]; lia
| left; apply Exists_cons_tl, Exists_cons_hd; unfold in_zr, A_REC_SPILL, SC_SIZE in *; cbn [fst snd]; lia
| ].
right. destruct (inFP_ablocks_fp_inv O a H) as (p & n & Hpn & Hr). exists p, n.
split; [apply in_or_app; left; exact (s1_O_blocks ly S rd R O HREP _ Hpn) | exact Hr].
Qed.
(* the stack above the callee's window and the side-stack frame are kept by a call whose footprint lies below
   alloc_ceiling and off the frame *)
Lemma s1_call_agree : forall STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 pos F lo hi,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (1, pos) (frames Sc) -> F = frame_addr lyc 1 pos ->
alloc_ceiling <= lo -> sp1 <= lo -> hi <= 2 ^ 64 ->
(forall a, inFP FP1 a -> a < alloc_ceiling /\ ~ (F <= a < F + 128)) ->
(forall a, lo <= a < hi -> rdW W2 mem2 a = rdW W memc a) /\
(forall a, F <= a < F + 128 -> rdW W2 mem2 a = rdW W memc a).
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 pos F lo hi HJc Hin EF Hlo Hsp Hhi HFP.
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & G1 & _ & _ & G4 & _).
split.
- intros a Ha. apply G1; [lia | lia | intros Hf; pose proof (HFP a Hf); lia].
- intros a Ha. apply (G4 1 pos a Hin).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. subst F. lia.
  + intros Hf. pose proof (HFP a Hf). lia.
Qed.
(* record()'s footprint at the call: below alloc_ceiling and off the side-stack frame (1, pos) *)
Lemma s1_recfp_off : forall ly S (W : world SEGS) mem md R O pos a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) -> In (1, pos) (frames S) ->
inFP (rca_recFP R O) a -> a < alloc_ceiling /\ ~ (frame_addr ly 1 pos <= a < frame_addr ly 1 pos + 128).
Proof using LAWS IMG.
intros ly S W mem md R O pos a HAR HOb Hin Ha.
pose proof alloc_ceiling_value as Ec.
destruct (s1_recfp R O a Ha) as (_ & [Hpg | Hb]).
- pose proof (CmdRecBase.cif_prog_img _ _ IMG a Hpg) as Himg.
  split.
  + unfold cmd_PG in Hpg. rewrite !inFP_cons in Hpg. pose proof (inFP_nil a).
    unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in Hpg. intuition lia.
  + intros Hf. apply (frm_img SEGS B LAWS ly S W mem md 1 pos a HAR Hin); [change (fs_frame_bytes 1) with 128; lia | exact Himg].
- destruct (inFP_ablocks_fp_inv O a Hb) as (p & n & Hpn & Hr).
  pose proof (HOb _ Hpn) as Hbl.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hbl) as (_ & _ & Hc & _).
  split; [lia|].
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n 1 pos HAR Hbl Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. lia.
Qed.
(* the block accounting after record(): its post (record_c.v:115-121) against the entry *)
Lemma s1_acct : forall ly S (O : list (Z * Z)) lyc Sc ly2 S2 (Fr O1 : list (Z * Z)),
List.NoDup (ablocks B lyc Sc) ->
ablocks B lyc Sc = ablocks B ly S -> blocks_bytes Sc = blocks_bytes S ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
Permutation (ablocks B lyc Sc) (ablocks B ly2 S2 ++ Fr) ->
(forall pn, In pn Fr -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn Fr) ->
blocks_bytes S2 <= blocks_bytes Sc ->
sa_acct B ly S O ly2 S2 O1 0.
Proof.
intros ly S O lyc Sc ly2 S2 Fr O1 HND Eab Ebb HOb HP HFO HO1 Hbb.
assert (HND2 : List.NoDup (ablocks B ly2 S2 ++ Fr)) by exact (Permutation_NoDup HP HND).
assert (Hin2 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly S)).
{ intros pn Hpn. rewrite <- Eab. eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_or_app; left; exact Hpn]. }
assert (Hin1 : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly2 S2) \/ In pn Fr).
{ intros pn Hpn. rewrite <- Eab in Hpn. apply in_app_or. eapply Permutation_in; [exact HP | exact Hpn]. }
unfold sa_acct. split; [|split; [|split; [|split]]].
- intros pn Hpn. left. exact (proj1 (proj1 (HO1 pn) Hpn)).
- intros pn Hpn. destruct (rca_in_dec pn O) as [Hi | Hi].
  + right. apply HO1. split; [exact Hi|]. intros HF. exact (list_nodup_app_disj _ _ pn HND2 Hpn HF).
  + left. split; [exact (Hin2 pn Hpn) | exact Hi].
- intros pn Hpn Hno. destruct (Hin1 pn Hpn) as [H | H]; [exact H | exfalso; exact (Hno (HFO pn H))].
- intros pn Hpn. destruct (proj1 (HO1 pn) Hpn) as [Hi Hnf].
  destruct (Hin1 pn (HOb pn Hi)) as [H | H]; [exact H | exfalso; exact (Hnf H)].
- lia.
Qed.
End e.
End f.
End d.
