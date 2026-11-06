(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the kit of the entry segment of answer's ASan walk (plugin-hostd/fuzz_command,
   0x8a4c0 .. 0x8a61c): the walk tactics answer_s1.v does not carry (as sup_resp's walk carried them over from
   cgif lib/A/ACkc.v), the symbolic entry state and its seed (cgif's flushFrame seed, lib/A/ACj0.v, as sup_resp's
   sr_entry), and the recorder's representation carried over a step that keeps the recorder's bytes. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_e1.v, with its module paths and module names changed; 726 of its 844 lines of code are new or changed and 156 lines of the source are left out. *)
(* sup_add's walk on the ASan build of plugin-hostd/fuzz_command, stage 1: the entry block 0x89dbc .. 0x89ee4
   (listing lines 2-76): the frame and the 13 saves, the realignment `andi sp,sp,-32`, the two spills, the shadow
   base and the use-after-return flag through their GOT words, the side-stack frame of class 1
   (__asan_stack_malloc_1), its header and shadow, g_rec's ncalls, then the branch `bne a0,a1` at 0x89ee4 into the
   table arm M0T (0x89f00) or the spill arm M0S (0x89ee8).

   The walk tactics and the realignment step are arg_i's walk's (lib/A/Prog/arg_i_s1.v and arg_i.v, from
   cgif's lib/A/ACkc.v), copied here with this file's prefix. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the walk tactics (arg_i_s1.v, from cgif lib/A/ACkc.v) ---- *)
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
Ltac s1_clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
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
Lemma s1_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 -> x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma s1_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma s1_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite s1_land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
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
Lemma s1_zr_apart : forall lo1 hi1 lo2 hi2, lo1 < hi1 -> lo2 < hi2 ->
(forall a, lo1 <= a < hi1 -> ~ (lo2 <= a < hi2)) -> hi1 <= lo2 \/ hi2 <= lo1.
Proof. intros lo1 hi1 lo2 hi2 H1 H2 H. destruct (Z_le_gt_dec hi1 lo2); [left; exact l|]. right.
destruct (Z_le_gt_dec hi2 lo1); [exact l|]. exfalso. apply (H (Z.max lo1 lo2)); lia. Qed.
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

(* ---- the entry state ---- *)
(* Atoms: the registers (0..31), the shadow base SB (32), the use-after-return flag's cell (33) and g_rec's ncalls
   (34). Regions: the 160-byte frame, the shadow GOT word and cell, the use-after-return GOT word and flag, and
   g_rec's ncalls (A_OBJ 44 = g_rec). The stage makes no inline check: no shadow entry. *)
Definition s1_Bx : sv := SOff 32 0.
Definition s1_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition s1_SH : list shent := [].
Definition s1_ncalls_region : YP09.region := YP09.mkRegion (Some (A_OBJ 44)) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 34 0))].
Definition s1_regions0 : smem :=
[ stack_region 160; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33; s1_ncalls_region ].
Definition s1_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0x10000 0x606000 2); (34%nat, mkAF 0 16 0) ].
Definition ss_s1 : sstate := mkSS AF_sup_add sr_atoms s1_regions0 None (mkFacts s1_atoms0 [] []).
Definition s1_extra (uar n : Z) : list word := map (Z_to_bv 64) [SB; uar; n].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s1_rec_PG : forall a, in_rec a -> inFP cmd_PG a.
Proof.
intros a Ha. unfold in_rec, cmd_PG, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *.
destruct Ha as [Ha | Ha]; [exists (6174528, 6174528 + 960) | exists (6175712, 6175712 + 56)]; cbn [In fst snd];
(split; [first [left; reflexivity | right; left; reflexivity] | lia]).
Qed.
Lemma s1_ncalls_rec : forall a, A_G_REC + 8 <= a < A_G_REC + 12 -> in_rec a.
Proof. intros a Ha. left. unfold REC_SIZE. lia. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
(* the record fact a heap string's word tail needs (a statement CmdRecFacts.v proves), CmdRecImg.v's lemma by exact *)
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* every byte of the program's statics is in the record's as_prog_static (CmdBSyms' ts_prog; arg_i_s1.v HPROG) *)
Lemma s1_HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hin & Hr). rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_exists.
unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr;
[exists (0x5e3740, 960) | exists (0x5e3be0, 56) | exists (0x5e3c60, 4)]; cbn [In];
(split; [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | unfold in_zr; cbn [fst snd]; lia]).
Qed.
(* the 13 saves of the real frame, from the stack region of the mid-state *)
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
Lemma s1_in_dec : forall (pn : Z * Z) (l : list (Z * Z)), {In pn l} + {~ In pn l}.
Proof. intros pn l. apply in_dec. decide equality; apply Z.eq_dec. Qed.
Lemma s1_bvrange : forall (r : bv 5) (regs : bvmap 5 word), 0 <= bv_unsigned (getr regs r) < 2 ^ 64.
Proof. intros r regs. pose proof (bv_unsigned_in_range 64 (getr regs r)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
(* the mid-state M0 from the facts the walk has at 0x89ee8 / 0x89f00 *)
Lemma s1_M0_ok : forall ly S W (regs : bvmap 5 word) mem md R O S2 (regs1 : bvmap 5 word) mem2 md2 fpos,
ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, fpos)] ly S2 W mem2 md2 0 ->
rec_repA B ly S (aview SEGS (w_H W) mem) R O ->
(forall pn, In pn O -> In pn (ablocks B ly S) /\ 1 <= snd pn) ->
(forall a, in_rec a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a) ->
(forall p k i, In (p, k) O -> 0 <= i < k -> aview SEGS (w_H W) mem2 (p + i) = aview SEGS (w_H W) mem (p + i)) ->
ablocks B ly S2 = ablocks B ly S -> blocks_bytes S2 = blocks_bytes S -> (exists f, S2 = set_fs f S) ->
sa_frame (aview SEGS (w_H W) mem2) (spZ regs) regs ->
aval_mem (aview SEGS (w_H W) mem2) (sa_s1 (spZ regs) + 16) 8 (bv_unsigned (getr regs 13)) ->
aval_mem (aview SEGS (w_H W) mem2) (sa_s1 (spZ regs) + 24) 8 (bv_unsigned (getr regs 12)) ->
aval_mem (aview SEGS (w_H W) mem2) (sa_s1 (spZ regs) + 48) 8 (frame_addr ly 1 fpos) ->
rdword (aview SEGS (w_H W) mem2) (frame_addr ly 1 fpos + fs_frame_bytes 1 - 8) = Some (flag_addr ly 1 fpos) ->
getr regs1 2 = w64 (sa_s1 (spZ regs)) -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
getr regs1 8 = w64 (spZ regs) -> getr regs1 9 = w64 (sa_s1 (spZ regs)) ->
getr regs1 18 = w64 (frame_addr ly 1 fpos) -> getr regs1 19 = getr regs 11 ->
getr regs1 21 = w64 A_G_REC -> getr regs1 25 = w64 (SHADOW_OFF + frame_addr ly 1 fpos / 8) ->
getr regs1 26 = w64 (frame_addr ly 1 fpos) ->
getr regs1 10 = w64 (Z.of_nat (length (r_calls R))) -> getr regs1 11 = w64 16 ->
getr regs1 20 = w64 SHADOW_OFF -> getr regs1 24 = getr regs 10 ->
sa_M0 B MT ly S W regs mem md R O ly S2 W regs1 mem2 md2 fpos.
Proof.
intros ly S W regs mem md R O S2 regs1 mem2 md2 fpos HJ HREP HOb TKr TKb Eab Hbb (f & ES2)
HFRM HV16 HV24 HV48 HFL Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q21 Q25 Q26 Q10 Q11 Q20 Q24.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S2)) by (intros pn Hpn; rewrite Eab; exact (proj1 (HOb pn Hpn))).
unfold sa_M0, sa_core. cbv zeta.
split.
{ split; [exact HJ|]. split; [exact HFRM|]. split; [exact HV16|]. split; [exact HV24|].
  split; [exact HV48|]. split; [exact HFL|]. split; [exact Q2|]. split; [exact Q3|].
  split; [exact Q4|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|].
  split; [exact Q19|]. split; [exact Q21|]. split; [exact Q25|]. exact Q26. }
split; [exact Q10|]. split; [exact Q11|]. split; [exact Q20|]. split; [exact Q24|].
split.
{ exact (rec_repA_kept B HB LAWS ly S (aview SEGS (w_H W) mem) ly S2
    (aview SEGS (w_H W) mem2) R O HREP TKr TKb HOin). }
split.
{ unfold sa_acct. split; [intros pn Hpn; left; exact Hpn|].
  split.
  { intros pn Hpn. rewrite Eab in Hpn. destruct (s1_in_dec pn O) as [Hin | Hni]; [right; exact Hin | left; split; [exact Hpn | exact Hni]]. }
  split; [intros pn Hpn _; rewrite Eab; exact Hpn|].
  split; [exact HOin | lia]. }
rewrite ES2. apply (mo_le_set_fs_r MT MTFL S S f 0). apply (mle_start MT S MTL).
Qed.
(* a byte of g_rec or record.spill is none of the record's cells, owned statics or errno *)
Lemma s1_rec_apart : forall ly S W mem md a, AR SEGS B ly S W mem md -> in_rec a ->
~ Exists (in_zr a) (asyms_areas B) /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros ly S W mem md a HAR Ha.
pose proof (prog_static_sep B a (am_syms _ _ _ _ (proj1 HAR)) (s1_HPROG a (s1_rec_PG a Ha))) as (H1 & H2 & H3). auto.
Qed.
Lemma s1_in_areas_cells : forall x len, In (x, len)
  [(as_shadow_cell B, 8); (as_uar_cell B, 4); (as_got_shadow B, 8); (as_got_uar B, 8)] -> In (x, len) (asyms_areas B).
Proof. intros x len H. unfold asyms_areas. cbn [In] in *. tauto. Qed.

Lemma s1_entry : forall W ly S regs mem md ch n,
afn_pre SEGS B SUP_ADD_STK ly S W regs mem md ch ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= n <= 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (s1_extra (as_uar_cell B) n))) ss_s1
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_add)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch n HPRE Hn Hn16.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : SUP_ADD_STK = 16768) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
assert (Hareas : forall x len, In (x, len) [(as_shadow_cell B, 8); (as_uar_cell B, 4); (as_got_shadow B, 8); (as_got_uar B, 8)] ->
  A_G_REC + 12 <= x \/ x + len <= A_G_REC + 8).
{ intros x len Hin.
  assert (Hlen : 0 < len) by (cbn [In] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as _ <-; lia|]); destruct Hin).
  apply s1_zr_apart; [unfold A_G_REC; lia | lia |]. intros a Ha Hx.
  apply (proj1 (s1_rec_apart ly S W mem md a HAR (s1_ncalls_rec a ltac:(lia)))). apply Exists_exists. exists (x, len).
  split; [exact (s1_in_areas_cells x len Hin) | unfold in_zr; cbn [fst snd]; lia]. }
pose proof (Hareas _ _ ltac:(cbn [In]; left; reflexivity)) as D12.
pose proof (Hareas _ _ ltac:(cbn [In]; right; left; reflexivity)) as Du.
pose proof (Hareas _ _ ltac:(cbn [In]; right; right; left; reflexivity)) as D0.
pose proof (Hareas _ _ ltac:(cbn [In]; right; right; right; left; reflexivity)) as D1.
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite (pal_got_shadow B TL) in D0. rewrite (pal_cell B TL) in D12. rewrite (palf_got_uar B TLF) in D1.
assert (V44 : VAL (A_OBJ 44) = A_G_REC) by (rewrite VOBJS by (vm_compute; lia); vm_compute; reflexivity).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (s1_extra (as_uar_cell B) n))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 (VAL (A_OBJ 44))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n0 v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
assert (B285 : base_val E (Some (A_OBJ 44)) = A_G_REC) by (rewrite (VB (A_OBJ 44) (VAL (A_OBJ 44)) E285), V44 by (rewrite V44; unfold A_G_REC; lia); reflexivity).
unfold ss_s1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s1_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, s1_ncalls_region.
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
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite B285. unfold A_G_REC. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ A_G_REC 8 4 (SOff 34 0) n);
  [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  intros k Hk. pose proof (Hn k Hk) as Hb. destruct (aview_byte SEGS (w_H W) mem _ _ Hb) as (b & Hm & Hbv & Hrange).
  unfold OFF_NCALLS, A_G_REC in Hm |- *. rewrite Hm. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite <- Hbv. unfold YO0f.le_byte, YG0f.le_byte. rewrite Z.mod_mod by lia. reflexivity.
- apply pairwise_disjoint_of_extents.
unfold s1_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, s1_ncalls_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B285, (VB 33%nat (as_uar_cell B) E33) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob1 Hob12 Huar Hsep D0 D1 D12 Du. clear.
unfold ASAN_CEIL, A_G_REC. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok s1_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, E34.
rewrite !unsigned_lit_small by (unfold SB in *; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
Qed.

Lemma sa_entry_ok : SA_M0T_stmt B MT -> SA_M0S_stmt B MT -> SA_ENTRY_stmt B MT.
Proof.
intros HM0T HM0S. unfold SA_ENTRY_stmt.
intros ly S W regs mem md ch pu id pp pc uri placement client R O CX.
pose proof CX as CX'. unfold sa_cx in CX'. cbv zeta in CX'.
destruct CX' as (HPRE & Hfr7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP & _).
pose proof (rec_repA_fields B HB LAWS ly S (rdW W mem) R O HREP) as HRF.
destruct HRF as (_ & _ & _ & _ & HNC & HN16 & _ & _ & HOb).
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn16 : 0 <= n <= 16) by (unfold n; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s1_entry W ly S regs mem md ch n HPRE HNC Hn16) as HS.
pose proof (ajournal_init SEGS B SUP_ADD_STK (sa_FP O) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : SUP_ADD_STK = 16768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs (s1_extra (as_uar_cell B) n))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n0 r Hn0; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (AG : forall n, (n < 32)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE.
assert (V44 : VAL (A_OBJ 44) = A_G_REC) by (rewrite VOBJS by (vm_compute; lia); vm_compute; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply (img_env_atomP E _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply (img_env_atomP E _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (apply (img_env_atomP E _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 0x5e3740) by (rewrite (img_env_atomP E _ HEI), V44 by (unfold A_OBJ, A_TEXT, A_LIM; lia); reflexivity).
change (A_OBJ 0) with 241%nat in E241 at 1. change (A_OBJ 1) with 242%nat in E242 at 1.
change (A_OBJ 12) with 253%nat in E253 at 1. change (A_OBJ 44) with 285%nat in E285.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold cfg_at. change (w64 (BASE + AF_sup_add)) with (Z_to_bv 64 (BASE + AF_sup_add)).
assert (SHOK : sh_ok SEGS s1_Bx s1_SH E (mrestrict (w_H W) mem)) by (unfold sh_ok, s1_SH; apply Forall_nil).
(* 0x89dbc .. 0x89dfc: the frame, the probe, the 13 saves, s0 := sp0, and the realignment *)
paj_run_to_tok RUNTO HS HJ SHOK s1_Bspan (AF_sup_add + 0x44).
{ awr_ok_tac. all: exact Usp. }
s1_md.
(* the memory below the stack is the entry memory *)
lazymatch goal with Hfr : frame_of ?Ef ?rs (mrestrict _ mem) (mrestrict _ ?m1) |- _ =>
assert (KL1 : forall a, 0 <= a < alloc_ceiling -> rdW W m1 a = rdW W mem a)
by (intros a Ha; apply (kept_of_frame (segs:=SEGS) Ef rs _ _ _ (fun a => alloc_ceiling <= a) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin
  | lia | lia ]) end.
clear HF HFr HG.
(* the realigned frame base sp1 = sa_s1 sp0: a fresh 32-aligned atom 35 in sp's place; the stack region keeps the
   saves [sp0 - 104, sp0), and atom 35's region [sp1, sp1 + 56) takes the spills and the frame pointer *)
set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (s1_sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by lia. clear Hsp1r.
assert (Hs1 : sa_s1 (spZ regs) = sp1).
{ assert (He : sp1 = 32 * ((spZ regs + -160) / 32)) by reflexivity. rewrite He. unfold sa_s1.
  pose proof (Z.div_mod (spZ regs + -160) 32 ltac:(lia)) as D.
  replace (spZ regs - 160) with (spZ regs + -160) by lia. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
s1_rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(s1_denot_and_m32 Ev 2 (spZ regs) (-160) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 35 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3; s1_hei_pose Ev 35%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. s1_rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E35 : ew Ev 35 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 35 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 35 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E35, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 35%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (s1_trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; s1_submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 35%nat) 0 56 0 56 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E35, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite FFS; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
s1_evalE AG; repeat split; lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
(* 0x89e00 .. 0x89e34: s1 := sp1, the spills, s3 := a1, the shadow base and the use-after-return flag (1, so `beqz` at
   0x89e2c falls through), s8 := a0, then the call of __asan_stack_malloc_1 for 96 bytes *)
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end.
lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
assert (SHOK : sh_ok sg s1_Bx s1_SH Ex (mrestrict (w_H Wx) (ms_mem msx))) by (unfold sh_ok, s1_SH; apply Forall_nil) end.
paj_run_tok RUN HS HJ SHOK s1_Bspan.
{ s1_awr AG ltac:(unfold awr_byte; left; lia). }
s1_md.
lazymatch goal with Hfr : frame_of ?Ef ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
assert (KL2 : forall a, 0 <= a < alloc_ceiling -> rdW W m2 a = rdW W mem a)
by (intros a Ha; rewrite <- (KL1 a Ha); apply (kept_of_frame (segs:=SEGS) Ef rs _ _ _ (fun a => alloc_ceiling <= a) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; s1_evalE AG; intros Hrr; lia|]); destruct Hin
  | lia | lia ]) end.
clear HF HFr HG KL1.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (palf_sm B TLF 1 ltac:(cbn [In]; right; left; reflexivity)) as Hsm1. cbn [cs_stack_malloc Z.eqb Pos.eqb] in Hsm1. rewrite Hsm1.
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
assert (Hfs1 : 16 <= fs_frames 1) by (vm_compute; intro Hq; discriminate Hq).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 1 (ASTACK_MALLOC1 fx) ltac:(lia) W rT mT SUP_ADD_STK (spZ regs) (sa_FP O)
    ly S W mem md [] ly S dT 0 (sp1 - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2, E35, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes. lia.
  - rewrite R3. s1_evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. s1_evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJs & (fS2 & ES2)).
(* the recorder's bytes after the call: g_rec / record.spill are image bytes the record does not own, the
   recorder's blocks are blocks the call keeps *)
assert (TK2 : (forall a, in_rec a -> rdW W mem2 a = rdW W mem a) /\
  (forall p k i, In (p, k) O -> 0 <= i < k -> rdW W mem2 (p + i) = rdW W mem (p + i))).
{ destruct HK as (K1 & K2 & K3 & _). split.
  - intros a Ha. destruct (s1_rec_apart ly S W mem md a HAR Ha) as (_ & Ho & Herr).
    rewrite (K3 a (cif_prog_img a (s1_rec_PG a Ha)) Ho Herr). apply KL2.
    unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. lia.
  - intros p k i Hin Hi. destruct (HOb (p, k) Hin) as (Hpk & Hk1 & _). cbn [snd] in Hk1.
    destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (Hp16 & Hp4096 & Hpceil & _).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
    rewrite (K2 p k i Hpk ltac:(lia) (fun H => H)). apply KL2. lia. }
clear KL2.
(* back at 0x89e38: keep atom 35's region, the saves and g_rec's ncalls *)
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (U2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (U285 : bv_unsigned (ew Ex 285) = A_G_REC) by (rewrite E285; reflexivity);
assert (U35 : bv_unsigned (ew Ex 35) = sp1) by (rewrite E35; apply unsigned_lit_small; lia) end.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 6]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U2, ?U285, ?U35; intros a Ha).
  - apply (mbyte_of_aview SEGS). apply K1; [lia | rewrite Hes; lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite FFS. lia.
  - apply (mbyte_of_aview SEGS). apply K1; [lia | rewrite Hes; lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite FFS. lia.
  - assert (Har : in_rec a) by (apply s1_ncalls_rec; lia).
    destruct (s1_rec_apart ly S W mem md a HAR Har) as (_ & Ho & Herr).
    apply (mbyte_of_aview SEGS). apply K3; [exact (cif_prog_img a (s1_rec_PG a Har)) | exact Ho | exact Herr].
  - lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 40 ?ws) _ _ =>
  assert (E44 : ew (havoc Eo 40 ws) 44 = Z_to_bv 64 (frame_addr ly 1 fpos)) by (etransitivity; [reflexivity | exact Ha0]) end.
s1_rebaseE HS AG HEv. clear HEv.
(* the side-stack frame F (class 1, 128 bytes), its flag FL and its shadow SB + F / 8 *)
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (FFL ly S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLapp & HFLrng).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in HFSpres.
fold F in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil, HFhigh. fold FL in HFLpres, HFLown, HFLapp, HFLrng.
assert (DRF : forall a, in_rec a -> ~ (F <= a < F + 128)).
{ intros a Ha Hb.
  pose proof (al_client_img _ _ LAWS ly S2 W mem2 md2 a HAR2
    ltac:(right; left; exists 1, fpos; split; [exact Hfin2 | fold F; change (fs_frame_bytes 1) with 128; lia])) as [_ Hni].
  exact (Hni (cif_prog_img a (s1_rec_PG a Ha))). }
assert (DFS : F + 128 <= A_G_REC + 8 \/ A_G_REC + 12 <= F).
{ apply s1_zr_apart; [lia | unfold A_G_REC; lia |]. intros a Ha Hb.
  exact (DRF a (s1_ncalls_rec a ltac:(lia)) ltac:(lia)). }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1028 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
s1_hei_pose Ev 1028%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. s1_rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E1028 : ew Ev 1028 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 1028 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E1029 : ew Ev 1029 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 1028 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 44 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E44, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1028 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E1028, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1029 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E1029, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 44 32 1029 F SB E44 ltac:(lia) E32 E1029)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 44%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 1028 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E44, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 120 8 _ FL);
  [cbn [sv_denot]; rewrite E1028, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
s1_evalE AG; unfold A_G_REC in DFS; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HF4096 HFceil DFS; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
assert (ZS : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz.
  lazymatch goal with |- _ <= _ < ?d => replace d with 16 by (vm_compute; reflexivity) end. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
  (fshadow_region 1029 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E1029, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
  apply (proj1 (HFSpres o ltac:(lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
  apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
  apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; s1_evalE AG; unfold SB; unfold A_G_REC in DFS;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HF4096 HFceil HFhigh HF8lo HF8hi HFq HF8 DFS; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
(* 0x89e38 .. 0x89ee4: s2 = s10 := F (`bnez` taken: F >= 4096), the frame header, the 12 shadow bytes through
   s9 = SB + F / 8, s5 := g_rec, a0 := ncalls, a1 := 16, the frame pointer at s1 + 48, up to `bne a0,a1` *)
paj_run_shc RUNP RUNC HS HJ2.
{ s1_awr_f AG fpos F. }
s1_md.
(* the recorder's bytes are none of the three writable windows of the frame's block *)
assert (NZr : forall a, in_rec a -> ~ (alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16)).
{ intros a Ha [Hq | [Hq | Hq]].
  - unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. lia.
  - exact (DRF a Ha Hq).
  - unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. unfold SB in Hq. lia. }
assert (NZb : forall p k i, In (p, k) O -> 0 <= i < k ->
  ~ (alloc_ceiling <= p + i \/ F <= p + i < F + 128 \/ SB + F / 8 <= p + i < SB + F / 8 + 16)).
{ intros p k i Hin Hi.
  destruct (HOb (p, k) Hin) as (Hpk & Hk1 & _). cbn [snd] in Hk1.
  assert (Hpk2 : In (p, k) (ablocks B ly S2)) by (rewrite Eab; exact Hpk).
  destruct (al_blocks _ _ LAWS ly S2 W mem2 md2 p k HAR2 Hpk2) as (Hp16 & Hp4096 & Hpceil & Hpapp & _).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
  pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 p k 1 fpos HAR2 Hpk2 Hfin2) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 1) with 128 in Hdj. fold F in Hdj.
  intros [Hq | [Hq | Hq]]; [lia | lia |].
  exact (fshadow_not_app F 16 p (req_size k) (p + i) ltac:(lia) ltac:(lia) Hpapp ltac:(unfold SB in Hq; lia) ltac:(lia)). }
(* run 3 writes only the stack, the frame and the frame's shadow *)
lazymatch goal with Hfr : frame_of ?Ef ?rs (mrestrict _ mem2) (mrestrict _ ?m3) |- _ =>
assert (KW3 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) ->
  rdW W m3 a = rdW W mem2 a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) Ef rs _ _ _
  (fun a => alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; s1_evalE AG; intros Hrr; lia|]); destruct Hin
  | exact Ha | exact Hn ]) end.
assert (TK3 : (forall a, in_rec a -> rdW W (ms_mem ms1) a = rdW W mem a) /\
  (forall p k i, In (p, k) O -> 0 <= i < k -> rdW W (ms_mem ms1) (p + i) = rdW W mem (p + i))).
{ split.
  - intros a Ha. rewrite (KW3 a ltac:(unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia) (NZr a Ha)).
    exact (proj1 TK2 a Ha).
  - intros p k i Hin Hi.
    destruct (HOb (p, k) Hin) as (Hpk & Hk1 & _). cbn [snd] in Hk1.
    destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (Hp16 & Hp4096 & Hpceil & _).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
    rewrite (KW3 (p + i) ltac:(lia) (NZb p k i Hin Hi)). exact (proj2 TK2 p k i Hin Hi). }
clear KW3 TK2.
assert (HOb2 : forall pn, In pn O -> In pn (ablocks B ly S) /\ 1 <= snd pn)
  by (intros pn Hpn; destruct (HOb pn Hpn) as (H1 & H2 & _); split; assumption).
assert (Hsp2 : getr regs 2 = w64 (spZ regs)) by (unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hnval : n = Z.of_nat (length (r_calls R))) by reflexivity.
assert (HRC64 : forall a, in_rec a -> 0 <= a < 2 ^ 64)
  by (intros a Ha; unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia).
assert (HOB64 : forall p k i, In (p, k) O -> 0 <= i < k -> 0 <= p + i < 2 ^ 64).
{ intros p k i Hin Hi. destruct (HOb (p, k) Hin) as (Hpk & Hk1 & _). cbn [snd] in Hk1.
  destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hreq]. lia. }
assert (HFdef : frame_addr ly 1 fpos = F) by reflexivity.
assert (HFLdef : flag_addr ly 1 fpos = FL) by reflexivity.
(* 0x89ee4: `bne a0,a1` on ncalls *)
psrr_branch_pi RUNP BR HS.
- (* taken: ncalls <> 16, the table arm at 0x89f00 *)
  assert (Hlt : (length (r_calls R) < 16)%nat).
  { rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc.
    rewrite (U_atom _ 34 n E34 ltac:(lia)), U_SLit in Hc. change (zcanon 16) with 16 in Hc. lia. }
  paj_run_to_sh RUNTOP HS HJ2 (AF_sup_add + 0x144).
  { s1_awr_f AG fpos F. }
  s1_md.
  lazymatch goal with Hfr : frame_of ?Ef ?rs (mrestrict _ ?m3) (mrestrict _ ?m4) |- _ =>
  assert (KW4 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) ->
    rdW W m4 a = rdW W m3 a)
  by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) Ef rs _ _ _
    (fun a => alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) Hfr);
    [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; s1_evalE AG; intros Hrr; lia|]); destruct Hin
    | exact Ha | exact Hn ]) end.
  pmkst HS.
  replace (BASE + 14876) with (BASE + L_M0T) by (unfold L_M0T, AF_sup_add; lia).
  eapply (HM0T ly S W regs mem md ch pu id pp pc uri placement client R O ly S2 W _ _ _ fpos CX); [| exact Hlt].
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 1%nat _ HS eq_refl) as HR44;
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 2%nat _ HS eq_refl) as HR35;
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 3%nat _ HS eq_refl) as HR2;
cbn [ms_mem restrict mkst] in HR44, HR35, HR2;
assert (U2x : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp);
assert (U35x : bv_unsigned (ew Ex 35) = sp1) by (rewrite E35; apply unsigned_lit_small; lia);
assert (U44x : bv_unsigned (ew Ex 44) = F) by (rewrite E44; apply unsigned_lit_small; lia);
assert (HEREG : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew Ex nn = getr regs rr)
  by (intros nn rr Hnn; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite (AG nn ltac:(lia)); apply EE; exact Hnn) end;
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (10%bv : bv 5) Q10;
prreg HS (11%bv : bv 5) Q11; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19;
prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (24%bv : bv 5) Q24;
prreg HS (25%bv : bv 5) Q25; prreg HS (26%bv : bv 5) Q26;
eapply s1_M0_ok;
[ exact HJ2
| exact HREP
| exact HOb2
| intros a Ha; rewrite (KW4 a (HRC64 a Ha) (NZr a Ha)); exact (proj1 TK3 a Ha)
| intros p k i Hin Hi; rewrite (KW4 (p + i) (HOB64 p k i Hin Hi) (NZb p k i Hin Hi)); exact (proj2 TK3 p k i Hin Hi)
| exact Eab
| exact Hbb2
| exists fS2; exact ES2
| exact (s1_frame_of_region _ _ _ _ _ _ _ HR2 U2x HEREG)
| rewrite Hs1; apply s1_aval_of_val_mem;
  apply (field_of_region _ _ 35%nat _ _ 0 56 0 56 16 8 (SOff 13 0) _ HR35 U35x);
  [ cbn; tauto
  | cbn [sv_denot]; rewrite (HEREG 13%nat (13%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; pose proof (s1_bvrange (13%bv : bv 5) regs); lia
  | cbn; lia ]
| rewrite Hs1; apply s1_aval_of_val_mem;
  apply (field_of_region _ _ 35%nat _ _ 0 56 0 56 24 8 (SOff 12 0) _ HR35 U35x);
  [ cbn; tauto
  | cbn [sv_denot]; rewrite (HEREG 12%nat (12%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; pose proof (s1_bvrange (12%bv : bv 5) regs); lia
  | cbn; lia ]
| rewrite Hs1, HFdef; apply s1_aval_of_val_mem;
  apply (field_of_region _ _ 35%nat _ _ 0 56 0 56 48 8 (SOff 44 0) _ HR35 U35x);
  [ cbn; tauto
  | cbn [sv_denot]; rewrite U44x, Z.add_0_r; reflexivity
  | cbn; lia
  | cbn; lia ]
| rewrite HFdef, HFLdef; change (fs_frame_bytes 1) with 128; replace (F + 128 - 8) with (F + 120) by lia;
  apply rdword_of_val_mem;
  [ apply (field_of_region _ _ 44%nat _ _ 0 128 0 128 120 8 (SOff 1028 0) _ HR44 U44x);
    [ cbn; tauto
    | cbn [sv_denot]; rewrite E1028, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia
    | cbn; lia ]
  | lia ]
| rewrite Q2, E35, Hs1; reflexivity
| rewrite Q3, (AG 3%nat ltac:(lia)), (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp
| rewrite Q4, (AG 4%nat ltac:(lia)), (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp
| rewrite Q8, (AG 2%nat ltac:(lia)), (EE 2%nat (2%bv : bv 5) eq_refl); exact Hsp2
| rewrite Q9, E35, Hs1; reflexivity
| rewrite HFdef, Q18, E44; reflexivity
| rewrite Q19, (AG 11%nat ltac:(lia)), (EE 11%nat (11%bv : bv 5) eq_refl); reflexivity
| rewrite Q21, E285; reflexivity
| rewrite HFdef, Q25, E1029; reflexivity
| rewrite HFdef, Q26, E44; reflexivity
| rewrite Q10, E34; reflexivity
| rewrite Q11; reflexivity
| rewrite Q20, E32; reflexivity
| rewrite Q24, (AG 10%nat ltac:(lia)), (EE 10%nat (10%bv : bv 5) eq_refl); reflexivity ].
- (* not taken: ncalls = 16, the spill arm at 0x89ee8 *)
  assert (Heq : length (r_calls R) = 16%nat).
  { rewrite branch_ne_U in Hc. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
    rewrite (U_atom _ 34 n E34 ltac:(lia)), U_SLit in Hc. change (zcanon 16) with 16 in Hc. lia. }
  paj_run_to_sh RUNTOP HS HJ2 (AF_sup_add + 0x12c).
  { s1_awr_f AG fpos F. }
  s1_md.
  lazymatch goal with Hfr : frame_of ?Ef ?rs (mrestrict _ ?m3) (mrestrict _ ?m4) |- _ =>
  assert (KW4 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) ->
    rdW W m4 a = rdW W m3 a)
  by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) Ef rs _ _ _
    (fun a => alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) Hfr);
    [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; s1_evalE AG; intros Hrr; lia|]); destruct Hin
    | exact Ha | exact Hn ]) end.
  pmkst HS.
  replace (BASE + 14852) with (BASE + L_M0S) by (unfold L_M0S, AF_sup_add; lia).
  eapply (HM0S ly S W regs mem md ch pu id pp pc uri placement client R O ly S2 W _ _ _ fpos CX); [| exact Heq].
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 1%nat _ HS eq_refl) as HR44;
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 2%nat _ HS eq_refl) as HR35;
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 3%nat _ HS eq_refl) as HR2;
cbn [ms_mem restrict mkst] in HR44, HR35, HR2;
assert (U2x : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp);
assert (U35x : bv_unsigned (ew Ex 35) = sp1) by (rewrite E35; apply unsigned_lit_small; lia);
assert (U44x : bv_unsigned (ew Ex 44) = F) by (rewrite E44; apply unsigned_lit_small; lia);
assert (HEREG : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew Ex nn = getr regs rr)
  by (intros nn rr Hnn; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite (AG nn ltac:(lia)); apply EE; exact Hnn) end;
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (10%bv : bv 5) Q10;
prreg HS (11%bv : bv 5) Q11; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19;
prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (24%bv : bv 5) Q24;
prreg HS (25%bv : bv 5) Q25; prreg HS (26%bv : bv 5) Q26;
eapply s1_M0_ok;
[ exact HJ2
| exact HREP
| exact HOb2
| intros a Ha; rewrite (KW4 a (HRC64 a Ha) (NZr a Ha)); exact (proj1 TK3 a Ha)
| intros p k i Hin Hi; rewrite (KW4 (p + i) (HOB64 p k i Hin Hi) (NZb p k i Hin Hi)); exact (proj2 TK3 p k i Hin Hi)
| exact Eab
| exact Hbb2
| exists fS2; exact ES2
| exact (s1_frame_of_region _ _ _ _ _ _ _ HR2 U2x HEREG)
| rewrite Hs1; apply s1_aval_of_val_mem;
  apply (field_of_region _ _ 35%nat _ _ 0 56 0 56 16 8 (SOff 13 0) _ HR35 U35x);
  [ cbn; tauto
  | cbn [sv_denot]; rewrite (HEREG 13%nat (13%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; pose proof (s1_bvrange (13%bv : bv 5) regs); lia
  | cbn; lia ]
| rewrite Hs1; apply s1_aval_of_val_mem;
  apply (field_of_region _ _ 35%nat _ _ 0 56 0 56 24 8 (SOff 12 0) _ HR35 U35x);
  [ cbn; tauto
  | cbn [sv_denot]; rewrite (HEREG 12%nat (12%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; pose proof (s1_bvrange (12%bv : bv 5) regs); lia
  | cbn; lia ]
| rewrite Hs1, HFdef; apply s1_aval_of_val_mem;
  apply (field_of_region _ _ 35%nat _ _ 0 56 0 56 48 8 (SOff 44 0) _ HR35 U35x);
  [ cbn; tauto
  | cbn [sv_denot]; rewrite U44x, Z.add_0_r; reflexivity
  | cbn; lia
  | cbn; lia ]
| rewrite HFdef, HFLdef; change (fs_frame_bytes 1) with 128; replace (F + 128 - 8) with (F + 120) by lia;
  apply rdword_of_val_mem;
  [ apply (field_of_region _ _ 44%nat _ _ 0 128 0 128 120 8 (SOff 1028 0) _ HR44 U44x);
    [ cbn; tauto
    | cbn [sv_denot]; rewrite E1028, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia
    | cbn; lia ]
  | lia ]
| rewrite Q2, E35, Hs1; reflexivity
| rewrite Q3, (AG 3%nat ltac:(lia)), (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp
| rewrite Q4, (AG 4%nat ltac:(lia)), (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp
| rewrite Q8, (AG 2%nat ltac:(lia)), (EE 2%nat (2%bv : bv 5) eq_refl); exact Hsp2
| rewrite Q9, E35, Hs1; reflexivity
| rewrite HFdef, Q18, E44; reflexivity
| rewrite Q19, (AG 11%nat ltac:(lia)), (EE 11%nat (11%bv : bv 5) eq_refl); reflexivity
| rewrite Q21, E285; reflexivity
| rewrite HFdef, Q25, E1029; reflexivity
| rewrite HFdef, Q26, E44; reflexivity
| rewrite Q10, E34; reflexivity
| rewrite Q11; reflexivity
| rewrite Q20, E32; reflexivity
| rewrite Q24, (AG 10%nat ltac:(lia)), (EE 10%nat (10%bv : bv 5) eq_refl); reflexivity ].
Qed.
End e.
End f.
End d.
