(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment LH of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command) from 0x86694 to the call of send_message: the symbolic state at 0x86694 and the walk through the two g_rec stores and the code-table load, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry: the seed lemma) and A/ACh5.v (a stretch between two points of one function). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI67 YN0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaLibF PaLibG.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01 LLVMFuzzerTestOneInput_s21
LLVMFuzzerTestOneInput_s22.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the imported `lia` (lib/Lib/LiaTwx2.v) fails on some linear goals here; fall back to the plain one *)
Ltac lhz1 := first [ lia | Zify.zify; xlia zchecker ].
Ltac lhz := first [ lhz1 | split; lhz1 | repeat split; lhz1 ].
(* a range goal over the walk's named constants *)
Ltac lhk := try unfold LT_SB; try unfold A_G_REC; try unfold LT_CODES; try unfold LT_NCODES;
  split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.

(* the shadow byte's address of x, as the code forms it: (x >> 3) + s1 *)
Definition lh_shw (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 9 0).
Definition lh_Bx : sv := SOff 9 0.
Definition lh_span : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
(* the frame words this stretch reads (the six shadow/table slots of LT_SLOTS and the two it writes at 104, 112),
   g_rec (its state and host words, and the first 8 bytes it writes) and the code table *)
Definition lh_stack_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 128 104 120
   [ YP09.mkChunk 16 (CVal 8 (SLit 7)); YP09.mkChunk 40 (CVal 8 (lh_shw (SOff 18 4)));
     YP09.mkChunk 48 (CVal 8 (lh_shw (SOff 18 952))); YP09.mkChunk 56 (CVal 8 (SOff (A_OBJ 40) 0));
     YP09.mkChunk 64 (CVal 8 (lh_shw (SOff 18 0))); YP09.mkChunk 72 (CVal 8 (lh_shw (SOff 18 944)));
     YP09.mkChunk 80 (CVal 8 (SLit 58)) ].
Definition lh_grec_region : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 960 0 8
   [ YP09.mkChunk 944 (CVal 8 (SOff 32 0)); YP09.mkChunk 952 (CVal 8 (SOff 33 0)) ].
Definition lh_codes_region : YP09.region := YP09.mkRegion (Some (A_OBJ 40)) 0 232 0 0 lh_chunks.
Definition lh_regions : smem := [lh_stack_region; lh_grec_region; lh_codes_region].
Definition lh_facts : facts :=
  mkFacts [ (2%nat, mkAF 70368744177664 140737488355328 4); (9%nat, mkAF LT_SB LT_SB 0); (18%nat, mkAF A_G_REC A_G_REC 6);
            (11%nat, mkAF 0 255 0); (32%nat, mkAF 0 18446744073709551615 0); (33%nat, mkAF 0 18446744073709551615 0);
            (A_OBJ 40, mkAF LT_CODES LT_CODES 5) ] [] [].
Definition ss_lh : sstate := mkSS LO_M1 sr_atoms lh_regions None lh_facts.
Definition lh_SH : list shent := [ mkSHE 18 0 960; mkSHE (A_OBJ 40) 0 232 ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition lh_extra (state host : Z) : list word := [Z_to_bv 64 state; Z_to_bv 64 host].
Definition lh_E (regs : bvmap 5 word) (state host : Z) : env := Eimg (Ereg regs (lh_extra state host)).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
#[local] Notation RRO := (cif_relro_img SEGS B IMG).

(* the walk hypothesis RPG, from CmdRecRest's cmd_ro_prog_apart: the program's statics are not read-only *)
Lemma lh_rpg : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a.
Proof.
intros a Ha Hro. destruct (cmd_ro_prog_apart SEGS B LAWS HB IMG a Hro) as [_ Hn]. apply Hn.
destruct Ha as (r & Hr & Har). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. unfold TFIB_PROG_STATIC.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Har;
[apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd];
unfold in_zr; cbn [fst snd]; lhz.
Qed.

Lemma lh_val_obj40 : VAL (A_OBJ 40) = LT_CODES.
Proof. rewrite (VOBJS 40%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). vm_compute. reflexivity. Qed.

(* the symbolic state at 0x86694: the seven frame words, g_rec's two read fields and the code table *)
Lemma lh_entry : forall cx ly S (W : world SEGS) (regs : bvmap 5 word) mem md k (R : rstate) O q b0,
lt_base B MT cx -> lt_frame B cx ly S W regs mem md k -> lt_slots cx (rdW W mem) ->
getr regs 9 = w64 LT_SB -> getr regs 18 = w64 A_G_REC -> getr regs 11 = w64 b0 -> 0 <= b0 < 256 ->
lt_rec B cx ly S W mem R O q [] ->
st_ok_pi SEGS VAL (lh_E regs (r_state R) (r_host R)) ss_lh
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_M1)) mem (seg_rom SEGS)))
/\ sh_ok SEGS lh_Bx lh_SH (lh_E regs (r_state R) (r_host R)) (mrestrict (w_H W) mem).
Proof.
intros cx ly S W regs mem md k R O q b0 Hbase Hfr Hslots H9 H18 H11 Rb0 Hrec.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hfr as (HJ & Hsp & _ & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (lt_ro_kept B MT LAWS HB IMG RRO lh_rpg cx ly S W mem md _ k Hbase HJ) as HRO.
destruct Hrec as (HR & _ & _ & _ & _ & _).
destruct HR as (Q & HQ & HO).
pose proof HQ as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & Hst & Hho & _ & _ & _ & Rst & Rho) & _).
(* sp of the frame *)
assert (Usp0 : spZ regs = x_sp1 cx) by exact Hsp.
assert (Hsp1a : x_sp1 cx mod 16 = 0).
{ unfold x_sp1, LT_FRAME. unfold x_sp0 in Hal16. rewrite Zminus_mod, Hal16. reflexivity. }
assert (Hsp1r : 70368744177664 <= x_sp1 cx <= 140737488355328).
{ unfold x_sp1, LT_FRAME. unfold x_sp0 in *. try unfold LLVMF_STK in *.
  change (2 ^ 47) with 140737488355328 in H47.
  remember (spZ (x_regs cx)) as sp0v eqn:E0. clear E0.
  remember (ly_stk_lo (x_ly cx)) as lov eqn:E1. clear E1.
  remember (ly_stk_hi (x_ly cx)) as hiv eqn:E2. clear E2.
  remember alloc_ceiling as acv eqn:E3. clear E3.
  clear - C1 Hceil Hslo Hshi H47 Hstk0. lhz. }
set (E := lh_E regs (r_state R) (r_host R)).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold lh_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (lh_extra (r_state R) (r_host R))) n)
  by (intros n Hn; subst E; unfold lh_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lhz); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = w64 LT_SB)
  by (rewrite EL by (unfold A_TEXT; lhz); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = w64 A_G_REC)
  by (rewrite EL by (unfold A_TEXT; lhz); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E11 : ew E 11 = w64 b0)
  by (rewrite EL by (unfold A_TEXT; lhz); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 (r_state R)) by (rewrite EL by (unfold A_TEXT; lhz); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (r_host R)) by (rewrite EL by (unfold A_TEXT; lhz); exact (ew_Ereg_extra regs _ 1)).
assert (EO40 : ew E (A_OBJ 40) = Z_to_bv 64 LT_CODES).
{ subst E. unfold lh_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lhz). rewrite lh_val_obj40. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = x_sp1 cx) by (rewrite E2; exact Hsp).
assert (U9 : bv_unsigned (ew E 9) = LT_SB) by (rewrite E9; apply unsigned_lit_small; unfold LT_SB; lhz).
assert (U18 : bv_unsigned (ew E 18) = A_G_REC) by (rewrite E18; apply unsigned_lit_small; unfold A_G_REC; lhz).
assert (U40 : bv_unsigned (ew E (A_OBJ 40)) = LT_CODES) by (rewrite EO40; apply unsigned_lit_small; unfold LT_CODES; lhz).
assert (U11 : bv_unsigned (ew E 11) = b0) by (rewrite E11; apply unsigned_lit_small; lhz).
assert (U32 : bv_unsigned (ew E 32) = r_state R) by (rewrite E32; apply unsigned_lit_small; lhz).
assert (U33 : bv_unsigned (ew E 33) = r_host R) by (rewrite E33; apply unsigned_lit_small; lhz).
(* the frame words, as values of the restricted memory *)
assert (SL : forall o v, In (o, v) LT_SLOTS -> val_mem SEGS (mrestrict (w_H W) mem) (x_sp1 cx + o) 8 v).
{ intros o v Hin. apply (val_mem_of_rdword SEGS). exact (Hslots o v Hin). }
assert (IN : forall o v, In (o, v) LT_SLOTS -> In (o, v) LT_SLOTS) by (intros; assumption).
split.
- unfold ss_lh. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold lh_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold lh_regions, lh_stack_region, lh_grec_region, lh_codes_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lhz|]. split; [lhz|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres.
        unfold x_sp1, x_sp0, LT_FRAME, LTOI_STK, LLVMF_STK in *. clear - Ho.
        remember (spZ (x_regs cx)) as sp0v eqn:E0. clear E0. lhz. }
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ (x_sp1 cx) 16 8 _ 7); [reflexivity | lhk | zside |].
         exact (SL 16 7 ltac:(unfold LT_SLOTS; cbn [In]; tauto)).
      -- apply (chunk_ok_val SEGS E _ (x_sp1 cx) 40 8 _ (LT_SB + (A_G_REC + 4) / 8));
           [unfold lh_shw; cbn [sv_denot]; rewrite E18, E9; vm_compute; reflexivity | lhk | zside |].
         exact (SL 40 _ ltac:(unfold LT_SLOTS; cbn [In]; tauto)).
      -- apply (chunk_ok_val SEGS E _ (x_sp1 cx) 48 8 _ (LT_SB + (A_G_REC + 952) / 8));
           [unfold lh_shw; cbn [sv_denot]; rewrite E18, E9; vm_compute; reflexivity | lhk | zside |].
         exact (SL 48 _ ltac:(unfold LT_SLOTS; cbn [In]; tauto)).
      -- apply (chunk_ok_val SEGS E _ (x_sp1 cx) 56 8 _ LT_CODES);
           [cbn [sv_denot]; rewrite EO40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lhk | zside |].
         exact (SL 56 _ ltac:(unfold LT_SLOTS; cbn [In]; tauto)).
      -- apply (chunk_ok_val SEGS E _ (x_sp1 cx) 64 8 _ (LT_SB + A_G_REC / 8));
           [unfold lh_shw; cbn [sv_denot]; rewrite E18, E9; vm_compute; reflexivity | lhk | zside |].
         exact (SL 64 _ ltac:(unfold LT_SLOTS; cbn [In]; tauto)).
      -- apply (chunk_ok_val SEGS E _ (x_sp1 cx) 72 8 _ (LT_SB + (A_G_REC + 944) / 8));
           [unfold lh_shw; cbn [sv_denot]; rewrite E18, E9; vm_compute; reflexivity | lhk | zside |].
         exact (SL 72 _ ltac:(unfold LT_SLOTS; cbn [In]; tauto)).
      -- apply (chunk_ok_val SEGS E _ (x_sp1 cx) 80 8 _ LT_NCODES); [reflexivity | lhk | zside |].
         exact (SL 80 _ ltac:(unfold LT_SLOTS; cbn [In]; tauto)).
    * rewrite U18. split; [unfold A_G_REC; lhz|]. split; [unfold A_G_REC; lhz|]. split.
      { intros o Ho. apply (PROG_WRITABLE SEGS B LAWS HB PRW). exists (A_G_REC, A_G_REC + 960).
        split; [left; reflexivity | cbn [fst snd]; clear - Ho; lhz]. }
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ A_G_REC 944 8 _ (r_state R));
           [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Rst | zside |].
         exact (val_mem_of_aval SEGS (w_H W) mem _ 8 _ Hst).
      -- apply (chunk_ok_val SEGS E _ A_G_REC 952 8 _ (r_host R));
           [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Rho | zside |].
         exact (val_mem_of_aval SEGS (w_H W) mem _ 8 _ Hho).
    * rewrite U40. split; [unfold LT_CODES; lhz|]. split; [unfold LT_CODES; lhz|].
      split; [intros o Ho; clear - Ho; lhz|].
      apply lh_chunks_ok. change LT_CODES with 0x21ba0. exact (lh_mbytes SEGS (w_H W) mem HRO).
  + apply pairwise_disjoint_of_extents.
    unfold lh_regions, lh_stack_region, lh_grec_region, lh_codes_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U18, U40.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold A_G_REC, LT_CODES. clear - Hsp1r. repeat split; lhz.
  + split; [|split; [exact I | exact I]].
    cbn [lh_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U9, U18, U11, U32, U33, U40.
    unfold LT_SB, A_G_REC, LT_CODES. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    try change (2 ^ 4) with 16. try change (2 ^ 6) with 64. try change (2 ^ 5) with 32.
    change (2 ^ 64) with 18446744073709551616 in Rst, Rho.
    clear - Hsp1r Hsp1a Rb0 Rst Rho.
    repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lhz].
- unfold sh_ok, lh_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E lh_Bx 18 A_G_REC 960 A_G_REC 0 960).
    * exact (cmd_addressable_chk SEGS B LAWS HB ly S W mem md A_G_REC 960 HAR ltac:(vm_compute; reflexivity)).
    * unfold U, lh_Bx. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold LT_SB; lhz). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold A_G_REC; lhz). reflexivity.
    * lhz. * lhz.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold A_G_REC, SHADOW_OFF in *. clear - Hx. lhz.
  + apply (shent_ok_of_range SEGS (w_H W) mem E lh_Bx (A_OBJ 40) LT_CODES 232 LT_CODES 0 232).
    * exact (cmd_addressable_chk SEGS B LAWS HB ly S W mem md LT_CODES 232 HAR ltac:(vm_compute; reflexivity)).
    * unfold U, lh_Bx. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold LT_SB; lhz). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite EO40, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold LT_CODES; lhz). reflexivity.
    * lhz. * lhz.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold LT_CODES, SHADOW_OFF in *. clear - Hx. lhz.
Qed.

(* ---- from the facts a run to the call of send_message leaves, to LT_SM_stmt ---- *)
Lemma lh_rdword_kept : forall (rd rd' : reader) a v, rdword rd a = Some v ->
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd' a = Some v.
Proof. intros rd rd' a v H HK. rewrite (rdword_ext rd rd' a HK). exact H. Qed.
Lemma lh_aval_of_val : forall H (mem : word -> option byte) a n v,
  val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Zmod_mod.
Qed.
Lemma lh_aval_mod32 : forall rd a v, aval_mem rd a 4 (v mod 2 ^ 32) -> aval_mem rd a 4 v.
Proof. intros rd a v H k Hk. rewrite (H k Hk). unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite Zmod_mod. reflexivity. Qed.
Lemma lh_codes_range : forall k, -2^31 <= nth k RecFacts.rec_codes 0 < 2^31.
Proof.
assert (H : forallb (fun r => (-2^31 <=? r) && (r <? 2^31)) RecFacts.rec_codes = true) by (vm_compute; reflexivity).
intros k. destruct (Nat.lt_ge_cases k (length RecFacts.rec_codes)) as [Hk|Hk].
- rewrite forallb_forall in H. specialize (H _ (nth_In _ 0 Hk)). apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. split; assumption.
- rewrite nth_overflow by exact Hk. change (2 ^ 31) with 2147483648. lhz.
Qed.
(* a byte of the frame outside the two words the stretch writes is kept *)
Lemma lh_keep_frame : forall (rd rd' : reader) s1 a,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 104 <= a < s1 + 120 \/ A_G_REC <= a < A_G_REC + 8) -> rd' a = rd a) ->
  A_G_REC + 8 <= s1 -> s1 + 256 <= 140737488355328 ->
  (s1 <= a < s1 + 104 \/ s1 + 120 <= a < s1 + 256) -> rd' a = rd a.
Proof.
intros rd rd' s1 a K H1 H2 Ha. unfold A_G_REC in *. apply K; [change (2 ^ 64) with 18446744073709551616; lhz|].
intros [Hb|Hb]; lhz.
Qed.
(* a byte below alloc_ceiling (a block's, or an image object's) outside g_rec's first 8 bytes is kept *)
Lemma lh_keep_low : forall (rd rd' : reader) s1 a,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 104 <= a < s1 + 120 \/ A_G_REC <= a < A_G_REC + 8) -> rd' a = rd a) ->
  0 <= a < s1 -> ~ (A_G_REC <= a < A_G_REC + 8) -> s1 + 256 <= 140737488355328 -> rd' a = rd a.
Proof.
intros rd rd' s1 a K H1 H2 H3. apply K; [change (2 ^ 64) with 18446744073709551616; lhz|].
intros [Hb|Hb]; [lhz | exact (H2 Hb)].
Qed.

Lemma lh_close : forall m, LT_SM_stmt B MT m ->
  forall cx ly S (W : world SEGS) regs mem md k acc r R O q regs' mem' md',
  lt_base B MT cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  lt_body B cx ly S W regs mem md k m -> 0 < r <= x_n cx ->
  getr regs 19 = w64 (lt_len (x_pl cx) (x_n cx) r) ->
  getr regs 20 = w64 (x_p cx + (x_n cx - r) + SlotSpec.hdr_n r) ->
  getr regs 21 = w64 (r - SlotSpec.hdr_n r) -> getr regs 27 = w64 (Z.of_nat m) ->
  lt_rec B cx ly S W mem R O q [] ->
  lt_bud MT cx S k acc (ev_from (32 - m) R (x_rest cx r)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 27 = getr regs 27 ->
  getr regs' 1 = w64 (BASE + LO_SMRA) -> getr regs' 10 = getr regs 20 -> getr regs' 11 = getr regs 19 ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp1 cx + 104 <= a < x_sp1 cx + 120 \/ A_G_REC <= a < A_G_REC + 8) ->
     rdW W mem' a = rdW W mem a) ->
  rdword (rdW W mem') (x_sp1 cx + LT_HOSTB) = Some (r_host R) ->
  rdword (rdW W mem') (x_sp1 cx + LT_STATEB) = Some (r_state R) ->
  aval_mem (rdW W mem') (A_G_REC + OFF_REFUSE) 4 (SlotSpec.msg_rf (lt_hdr (x_pl cx) (x_n cx) r)) ->
  aval_mem (rdW W mem') (A_G_REC + OFF_CODE) 4 (SlotSpec.msg_cd (lt_hdr (x_pl cx) (x_n cx) r)) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_send_message)) mem' (seg_rom SEGS)) md') (lt_post B MT cx).
Proof.
intros m HSM cx ly S W regs mem md k acc r R O q regs' mem' md' Hbase HFP Hbody Hr H19 H20 H21 H27 Hrec Hbud
  K2 K3 K4 K8 K9 K18 K19 K20 K21 K22 K27 R1 R10 R11 HJ' KEEP Hhost Hstate Hrf Hcd.
pose proof Hbody as (Hfr & Hslots & R8 & R9 & R18 & R22 & Hm & Hn & Hp).
pose proof Hfr as (HJ & Hsp & Hgp & Htp & Hsaved).
pose proof Hbase as (_ & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hs1lo : alloc_ceiling + 256 <= x_sp1 cx /\ x_sp1 cx + 256 <= 140737488355328).
{ unfold x_sp1, x_sp0, LT_FRAME, LTOI_STK, LLVMF_STK in *. change (2 ^ 47) with 140737488355328 in H47.
  remember (spZ (x_regs cx)) as s0 eqn:E0. clear E0. remember (ly_stk_lo (x_ly cx)) as lo eqn:E1. clear E1.
  remember (ly_stk_hi (x_ly cx)) as hi eqn:E2. clear E2. remember alloc_ceiling as ac eqn:E3. clear E3.
  clear - Hceil Hslo Hshi H47. lhz. }
assert (Hs1g : A_G_REC + 960 <= x_sp1 cx /\ A_REC_SPILL + 56 <= x_sp1 cx /\ A_G_QUITTING + 4 <= x_sp1 cx).
{ destruct Hs1lo as [Hs1lo _]. unfold A_G_REC, A_REC_SPILL, A_G_QUITTING.
  remember (x_sp1 cx) as s1 eqn:E0. clear E0. remember alloc_ceiling as ac eqn:E3. clear E3.
  clear - C1 Hs1lo. lhz. }
destruct Hs1lo as [Hs1lo Hs1hi]. destruct Hs1g as (Hs1g & Hs1s & Hs1q).
assert (Hx01 : x_sp0 cx = x_sp1 cx + 256) by (unfold x_sp1, x_sp0, LT_FRAME; ring).
(* bytes kept: the frame outside the two written words, and everything below the frame outside g_rec's first 8 *)
assert (KF : forall a, (x_sp1 cx <= a < x_sp1 cx + 104 \/ x_sp1 cx + 120 <= a < x_sp1 cx + 256) ->
  rdW W mem' a = rdW W mem a).
{ intros a Ha. apply (lh_keep_frame _ _ (x_sp1 cx) a KEEP); [| exact Hs1hi | exact Ha].
  remember (x_sp1 cx) as s1 eqn:E0. clear E0. clear - Hs1g. unfold A_G_REC in *. lhz. }
assert (KL : forall a, 0 <= a < x_sp1 cx -> ~ (A_G_REC <= a < A_G_REC + 8) -> rdW W mem' a = rdW W mem a).
{ intros a Ha Hg. exact (lh_keep_low _ _ (x_sp1 cx) a KEEP Ha Hg Hs1hi). }
cbv zeta in HSM.
apply (HSM cx ly S W regs' mem' md' k acc r R O q Hbase HFP).
- (* lt_body *)
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  + split; [exact HJ'|]. split; [unfold spZ; rewrite K2; exact Hsp|].
    split; [rewrite K3; exact Hgp|]. split; [rewrite K4; exact Htp|].
    intros i0 r0 Hi0. specialize (Hsaved i0 r0 Hi0).
    assert (Hi13 : (i0 < 13)%nat) by (change 13%nat with (length LT_SAVED); apply nth_error_Some; rewrite Hi0; discriminate).
    apply (lh_rdword_kept _ _ _ _ Hsaved). intros j Hj. apply KF. rewrite Hx01.
    remember (x_sp1 cx) as s1 eqn:E0. clear E0. clear - Hi13 Hj. lhz.
  + intros o v Hin. specialize (Hslots o v Hin).
    assert (Ho : 0 <= o <= 80).
    { assert (HB0 : forallb (fun p => (0 <=? fst p) && (fst p <=? 80)) LT_SLOTS = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in HB0. specialize (HB0 _ Hin). cbn [fst] in HB0.
      apply andb_prop in HB0 as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; assumption. }
    apply (lh_rdword_kept _ _ _ _ Hslots). intros j Hj. apply KF.
    remember (x_sp1 cx) as s1 eqn:E0. clear E0. clear - Ho Hj. lhz.
  + rewrite K8. exact R8.
  + rewrite K9. exact R9.
  + rewrite K18. exact R18.
  + rewrite K22. exact R22.
  + split; [exact Hm|]. split; [exact Hn | exact Hp].
- (* lt_msg_regs *)
  split; [exact Hr|]. split; [rewrite K19; exact H19|]. split; [rewrite K20; exact H20|].
  split; [rewrite K21; exact H21|]. split; [rewrite K27; exact H27|]. split; [exact Hhost | exact Hstate].
- exact R1.
- rewrite R10. exact H20.
- rewrite R11. exact H19.
- (* the recorder with g_rec.refuse and g_rec.code set *)
  destruct Hrec as (HR & Hsp0 & H2 & Hq & Rq & HP).
  assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
  { intros pn Hpn. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hpn. }
  unfold lt_R0. split; [|split; [exact Hsp0|split; [exact H2|split; [|split; [exact Rq | exact HP]]]]].
  + apply (lh_rec_repA_rc B ly S (rdW W mem) ly S (rdW W mem') R O _ _ HR HOin Hrf Hcd).
    * unfold SlotSpec.msg_rf. pose proof (Z.mod_pos_bound (SlotSpec.hbyte (lt_hdr (x_pl cx) (x_n cx) r) 0) 2 ltac:(lia)).
      change (2 ^ 31) with 2147483648. lhz.
    * unfold SlotSpec.msg_cd. exact (lh_codes_range _).
    * intros a Ha. apply KL; [|unfold OFF_NCALLS, REC_SIZE, A_G_REC in *; lhz].
      unfold OFF_NCALLS, REC_SIZE in Ha. remember (x_sp1 cx) as s1 eqn:E0. clear E0. clear - Ha Hs1g. unfold A_G_REC in *. lhz.
    * intros a Ha. apply KL; [|unfold SC_SIZE, A_REC_SPILL, A_G_REC in *; lhz].
      unfold SC_SIZE in Ha. remember (x_sp1 cx) as s1 eqn:E0. clear E0. clear - Ha Hs1s. unfold A_REC_SPILL in *. lhz.
    * intros p n i Hpn Hi. pose proof (HOin _ Hpn) as Hpn'.
      destruct (al_blocks _ _ LAWS ly S W mem md p n (proj1 HJ) Hpn') as (_ & Hp4096 & Hpceil & _).
      pose proof (blk_off_imgP B _ _ _ _ _ _ _ (proj1 HJ) Hpn') as Hoff.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
      apply KL.
      -- remember (x_sp1 cx) as s1 eqn:E0. clear E0. remember alloc_ceiling as ac eqn:E3. clear E3.
         remember (req_size n) as rn eqn:E4. clear E4. clear - Hi Hp4096 Hpceil Hreq Hs1lo. lhz.
      -- unfold off_img in Hoff. unfold A_G_REC. remember (req_size n) as rn eqn:E4. clear E4.
         clear - Hi Hreq Hoff. lhz.
  + apply (lh_aval_kept (rdW W mem)); [exact Hq|]. intros j Hj. apply KL.
    * remember (x_sp1 cx) as s1 eqn:E0. clear E0. clear - Hj Hs1q. unfold A_G_QUITTING in *. lhz.
    * unfold A_G_QUITTING, A_G_REC. clear - Hj. lhz.
- (* the budget: one pass of ev_from *)
  replace (32 - m)%nat with (Datatypes.S (31 - m)) in Hbud by lia.
  unfold x_rest in *. rewrite (ev_from_S (31 - m) R (x_pl cx) (x_n cx) r Hlen Hr) in Hbud. exact Hbud.
Qed.

(* ---- the two values the stretch computes from the flags byte b0: the index (b0 >> 1) % 58 (remw) and the
   refusal bit b0 & 1, as closed functions checked over the 256 bytes ---- *)
Definition lh_rem_sv : sv := SMdw M_REM (SAlu ALU_SRL (SOff 11 0) (SLit 1)) (SLit 58).
Definition lh_remf (w : word) : word :=
  sext 64 (mul_div M_REM (low32 (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned w + 0)) (Z_to_bv 64 1)))
    (low32 (Z_to_bv 64 58))).
Lemma lh_remf_val : forall b0, 0 <= b0 < 256 -> lh_remf (Z_to_bv 64 b0) = Z_to_bv 64 ((b0 / 2) mod 58).
Proof.
assert (H : forallb (fun k => bv_eqb (lh_remf (Z_to_bv 64 (Z.of_nat k))) (Z_to_bv 64 ((Z.of_nat k / 2) mod 58)))
  (seq 0 256) = true) by (vm_compute; reflexivity).
intros b0 Hb. rewrite forallb_forall in H. specialize (H (Z.to_nat b0) ltac:(apply in_seq; lhz)).
unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq.
replace (Z.of_nat (Z.to_nat b0)) with b0 in H by lhz. exact H.
Qed.
Lemma lh_rem_val : forall E b0, 0 <= b0 < 256 -> ew E 11 = Z_to_bv 64 b0 ->
  sv_denot E lh_rem_sv = Z_to_bv 64 ((b0 / 2) mod 58).
Proof.
intros E b0 Hb H11. pose proof (lh_remf_val b0 Hb) as HF. unfold lh_remf in HF.
unfold lh_rem_sv. cbn [sv_denot]. rewrite H11. exact HF.
Qed.
Definition lh_andf (w : word) : word := alu64 ALU_AND (Z_to_bv 64 (bv_unsigned w + 0)) (Z_to_bv 64 1).
Lemma lh_andf_val : forall b0, 0 <= b0 < 256 ->
  bv_unsigned (lh_andf (Z_to_bv 64 b0)) mod 2 ^ (8 * Z.of_N 4) = b0 mod 2.
Proof.
assert (H : forallb (fun k => Z.eqb (bv_unsigned (lh_andf (Z_to_bv 64 (Z.of_nat k))) mod 2 ^ (8 * Z.of_N 4))
  (Z.of_nat k mod 2)) (seq 0 256) = true) by (vm_compute; reflexivity).
intros b0 Hb. rewrite forallb_forall in H. specialize (H (Z.to_nat b0) ltac:(apply in_seq; lhz)).
apply Z.eqb_eq in H. replace (Z.of_nat (Z.to_nat b0)) with b0 in H by lhz. exact H.
Qed.
Lemma lh_refuse_val : forall E b0, 0 <= b0 < 256 -> ew E 11 = Z_to_bv 64 b0 ->
  bv_unsigned (sv_denot E (SAlu ALU_AND (SOff 11 0) (SLit 1))) mod 2 ^ (8 * Z.of_N 4) = b0 mod 2.
Proof.
intros E b0 Hb H11. pose proof (lh_andf_val b0 Hb) as HF. unfold lh_andf in HF.
cbn [sv_denot]. rewrite H11. exact HF.
Qed.

Lemma lh_E_reg : forall regs s h n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (lh_E regs s h) n = getr regs rr.
Proof.
intros regs s h n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold lh_E. rewrite Eimg_low by (unfold A_TEXT; lhz). apply ew_Ereg_nat. exact Hn.
Qed.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* the writes a run of this stretch may make: the frame words at 104 .. 120 (below the entry's sp, d = -256) and
   g_rec's first 8 bytes (a program static in cmd_PG); the code table is read-only *)
Ltac lh_awr Usp U18 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc fr ly own) end;
  eapply awr_ok_cons_stack_off;
  [ reflexivity
  | first [rewrite Usp | cbn [ew ewset extK Nat.eqb]; rewrite Usp]; unfold x_sp1, x_sp0, LT_FRAME;
    rewrite <- Z.add_opp_r; reflexivity
  | apply Z.leb_le; vm_compute; reflexivity
  | apply Z.leb_le; vm_compute; reflexivity | ];
  eapply awr_ok_cons_gen;
  [ reflexivity
  | first [exact U18 | cbn [ew ewset extK Nat.eqb]; exact U18]
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hfp := fresh "Hfp" in
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
    assert (Hfp : inFP cmd_PG a)
      by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; clear - Ha; lhz]);
    right; right; right; right; left; split; [exact Hfp|]; split;
    [ rewrite (ts_prog B HB); unfold TFIB_PROG_STATIC; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
      unfold A_G_REC in Ha; clear - Ha; lhz
    | exact (proj1 (cmd_prog_unowned SEGS B LAWS HB IMG a Hfp)) ]
  | ];
  apply awr_ok_cons_ro; [apply Z.leb_le; vm_compute; reflexivity | ]; apply awr_ok_nil.

(* what a run of this stretch keeps: every byte outside its two write windows *)
Ltac lh_keep HFr Usp U18 cx KEEP :=
  lazymatch type of HFr with
  | frame_of ?E0 ?rs (mrestrict (w_H ?W0) ?m0) (mrestrict _ ?m1) =>
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
      ~ (x_sp1 cx + 104 <= a < x_sp1 cx + 120 \/ A_G_REC <= a < A_G_REC + 8) ->
      aview SEGS (w_H W0) m1 a = aview SEGS (w_H W0) m0 a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
      intros a Ha Hn;
      apply (kept_of_frame (segs:=SEGS) E0 rs (w_H W0) m0 m1
        (fun a => x_sp1 cx + 104 <= a < x_sp1 cx + 120 \/ A_G_REC <= a < A_G_REC + 8) HFr); [| exact Ha | exact Hn];
      let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
      let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
      intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U18 in Hrr;
         first [left; exact Hrr | right; rewrite ?Z.add_0_r in Hrr; exact Hrr | exfalso; clear - Hrr; lhz] |]);
      destruct Hin
    | ]
  end.

Lemma lh_mid : forall m, LTA_SM B MT m -> LH_M1_stmt B MT m.
Proof.
intros m HSMA. pose proof (HSMA fx) as HSM. clear HSMA. unfold LH_M1_stmt.
intros cx ly S W regs mem md k acc r R O q Hbase HFP Hbody Hr H11 H19 H20 H21 H27 Hrec Hbud.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof Hbody as (Hfr & Hslots & R8 & R9 & R18 & R22 & Hm & Hn & Hp).
pose proof Hfr as (HJ & Hsp & Hgp & Htp & Hsaved).
pose proof Hrec as ((Q & HQ & HO) & _).
pose proof HQ as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Rst & Rho) & _).
clear Q HQ HO.
remember (SlotSpec.hbyte (lt_hdr (x_pl cx) (x_n cx) r) 0) as b0 eqn:Eb0.
assert (Rb0 : 0 <= b0 < 256).
{ rewrite Eb0. unfold SlotSpec.hbyte.
  pose proof (bv_unsigned_in_range 8 (nth 0 (lt_hdr (x_pl cx) (x_n cx) r) (Z_to_bv 8 0))) as HH.
  change (bv_modulus 8) with 256 in HH. exact HH. }
destruct (lh_entry cx ly S W regs mem md k R O q b0 Hbase Hfr Hslots R9 R18 H11 Rb0 Hrec) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (lh_E regs (r_state R) (r_host R))) by (unfold lh_E; apply Eimg_env).
assert (E2 : ew (lh_E regs (r_state R) (r_host R)) 2 = getr regs 2) by (apply lh_E_reg; reflexivity).
assert (E11 : ew (lh_E regs (r_state R) (r_host R)) 11 = Z_to_bv 64 b0)
  by (rewrite (lh_E_reg _ _ _ 11 11%bv eq_refl); exact H11).
assert (E18 : ew (lh_E regs (r_state R) (r_host R)) 18 = w64 A_G_REC)
  by (rewrite (lh_E_reg _ _ _ 18 18%bv eq_refl); exact R18).
assert (E32 : ew (lh_E regs (r_state R) (r_host R)) 32 = Z_to_bv 64 (r_state R))
  by (unfold lh_E; rewrite Eimg_low by (unfold A_TEXT; lhz); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (lh_E regs (r_state R) (r_host R)) 33 = Z_to_bv 64 (r_host R))
  by (unfold lh_E; rewrite Eimg_low by (unfold A_TEXT; lhz); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew (lh_E regs (r_state R) (r_host R)) 2) = x_sp1 cx) by (rewrite E2; exact Hsp).
assert (U18 : bv_unsigned (ew (lh_E regs (r_state R) (r_host R)) 18) = A_G_REC)
  by (rewrite E18; apply unsigned_lit_small; unfold A_G_REC; lhz).
assert (EK : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (lh_E regs (r_state R) (r_host R)) n = getr regs rr)
  by (intros n rr Hn0; apply lh_E_reg; exact Hn0).
remember (lh_E regs (r_state R) (r_host R)) as E eqn:HE.
clear HE.
(* 0x86694 .. 0x866d4: the two g_rec words and their shadow (shadow entries), g_rec.refuse := b0 & 1, the index
   (b0 >> 1) remw 58 in a0 *)
paj_run_to_tok RUNTO HS HJ SHOK lh_span 0x1f0.
{ lh_awr Usp U18. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
lh_keep HFr Usp U18 cx KEEP1.
clear HF HFr HG.
rename ms into ms1.
assert (A10 : getr (ms_regs ms1) 10 = Z_to_bv 64 ((b0 / 2) mod 58)).
{ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms1 10%bv HS).
  lazymatch goal with |- context [sr_get (ss_regs ?X) _] =>
    let e := eval vm_compute in (sr_get (ss_regs X) 10%bv) in change (sr_get (ss_regs X) 10%bv) with e end.
  change (SMdw M_REM (SAlu ALU_SRL (SOff 11 0) (SLit 1)) (SLit 58)) with lh_rem_sv.
  exact (lh_rem_val E b0 Rb0 E11). }
assert (Hix : exists i, (i < 58)%nat /\ (b0 / 2) mod 58 = Z.of_nat i).
{ pose proof (Z.mod_pos_bound (b0 / 2) 58 ltac:(lhz)) as Hx. remember ((b0 / 2) mod 58) as x eqn:Ex. clear Ex.
  exists (Z.to_nat x). clear - Hx. split; lhz. }
destruct Hix as (i & Hi & Hidx). rewrite Hidx in A10.
assert (Hcd : SlotSpec.msg_cd (lt_hdr (x_pl cx) (x_n cx) r) = nth i RecFacts.rec_codes 0).
{ unfold SlotSpec.msg_cd. rewrite <- Eb0. f_equal. rewrite Hidx. apply Nat2Z.id. }
assert (Hrf : SlotSpec.msg_rf (lt_hdr (x_pl cx) (x_n cx) r) = b0 mod 2) by (unfold SlotSpec.msg_rf; rewrite <- Eb0; reflexivity).
clear Hidx.
(* 0x866d4 .. 0x86714, once per index: the code table entry, its shadow (the table's shadow entry), g_rec.code,
   the two frame words, and the call of send_message *)
do 58 (destruct i as [|i]; [
  let HS2 := fresh "HS2" in
  pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv _ HS A10 eq_refl) as HS2; clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK lh_span;
  [ lh_awr Usp U18
  | lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end;
    lh_keep HFr Usp U18 cx KEEP2;
    pmkst HS;
    rewrite (SIGP CS_send_message ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])));
    replace (cmd_af CS_send_message) with AF_send_message by (vm_compute; reflexivity);
    let Ef := lazymatch type of HS with st_ok _ ?Ef _ _ => Ef end in
    let X := lazymatch type of HS with st_ok _ _ (setpc ?X _) _ => X end in
    assert (F2 : ew Ef 2 = ew E 2) by (first [reflexivity | cbn [ew ewset Nat.eqb]; reflexivity]);
    assert (F11 : ew Ef 11 = Z_to_bv 64 b0) by (first [exact E11 | cbn [ew ewset Nat.eqb]; exact E11]);
    assert (F18 : ew Ef 18 = ew E 18) by (first [reflexivity | cbn [ew ewset Nat.eqb]; reflexivity]);
    assert (F32 : ew Ef 32 = Z_to_bv 64 (r_state R)) by (first [exact E32 | cbn [ew ewset Nat.eqb]; exact E32]);
    assert (F33 : ew Ef 33 = Z_to_bv 64 (r_host R)) by (first [exact E33 | cbn [ew ewset Nat.eqb]; exact E33]);
    let rg0 := eval vm_compute in (nth 0 (ss_mem X) lh_stack_region) in
    let rg1 := eval vm_compute in (nth 1 (ss_mem X) lh_stack_region) in
    pose proof (YI67.st_chunk_val SEGS Ef _ _ 0 rg0 2 104 8 (SOff 33 0) (x_sp1 cx) (r_host R) HS eq_refl eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
      ltac:(first [exact Usp | rewrite F2; exact Usp])
      ltac:(cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Rho) ltac:(cbn; lhz)) as VH;
    pose proof (YI67.st_chunk_val SEGS Ef _ _ 0 rg0 2 112 8 (SOff 32 0) (x_sp1 cx) (r_state R) HS eq_refl eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
      ltac:(first [exact Usp | rewrite F2; exact Usp])
      ltac:(cbn [sv_denot]; rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Rst) ltac:(cbn; lhz)) as VS;
    pose proof (YN0d.st_ok_chunk SEGS Ef _ _ 1 rg1 (YP09.mkChunk 0 (CVal 4 (SAlu ALU_AND (SOff 11 0) (SLit 1)))) HS eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))) as CR;
    pose proof (val_of_chunk_any SEGS Ef _ _ 0 4 _ CR ltac:(cbn; lhz)) as VR;
    cbn [base_val YP09.r_base] in VR; (try rewrite F18 in VR); rewrite U18 in VR; rewrite (lh_refuse_val Ef b0 Rb0 F11) in VR;
    let cu := eval vm_compute in (match List.find (fun c => Z.eqb (YP09.c_off c) 4) (YP09.r_chunks rg1) with
                                  | Some (YP09.mkChunk _ (CVal _ e)) => e | _ => SLit 0 end) in
    pose proof (YN0d.st_ok_chunk SEGS Ef _ _ 1 rg1 (YP09.mkChunk 4 (CVal 4 cu)) HS eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))) as CC;
    pose proof (val_of_chunk_any SEGS Ef _ _ 4 4 _ CC ltac:(cbn; lhz)) as VC;
    cbn [base_val YP09.r_base] in VC; (try rewrite F18 in VC); rewrite U18 in VC;
    let ix := lazymatch type of Hcd with _ = nth ?ix _ _ => ix end in
    replace (bv_unsigned (sv_denot Ef cu) mod 2 ^ (8 * Z.of_N 4)) with (nth ix RecFacts.rec_codes 0 mod 2 ^ 32) in VC
      by (cbn [sv_denot]; vm_compute; reflexivity);
    prreg HS (1%bv : bv 5) P1; prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
    prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (10%bv : bv 5) P10; prreg HS (11%bv : bv 5) P11;
    prreg HS (18%bv : bv 5) P18; prreg HS (19%bv : bv 5) P19; prreg HS (20%bv : bv 5) P20;
    prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22; prreg HS (27%bv : bv 5) P27;
    apply (lh_close m HSM cx ly S W regs mem md k acc r R O q _ _ _ Hbase HFP Hbody Hr H19 H20 H21 H27 Hrec Hbud);
    [ rewrite P2; exact (EK 2%nat 2%bv eq_refl) | rewrite P3; exact (EK 3%nat 3%bv eq_refl)
    | rewrite P4; exact (EK 4%nat 4%bv eq_refl) | rewrite P8; exact (EK 8%nat 8%bv eq_refl)
    | rewrite P9; exact (EK 9%nat 9%bv eq_refl) | rewrite P18; exact (EK 18%nat 18%bv eq_refl)
    | rewrite P19; exact (EK 19%nat 19%bv eq_refl) | rewrite P20; exact (EK 20%nat 20%bv eq_refl)
    | rewrite P21; exact (EK 21%nat 21%bv eq_refl) | rewrite P22; exact (EK 22%nat 22%bv eq_refl)
    | rewrite P27; exact (EK 27%nat 27%bv eq_refl)
    | rewrite P1; reflexivity
    | rewrite P10; exact (EK 20%nat 20%bv eq_refl) | rewrite P11; exact (EK 19%nat 19%bv eq_refl)
    | exact HJ
    | intros a Ha Hn0; rewrite (KEEP2 a Ha Hn0); exact (KEEP1 a Ha Hn0)
    | apply (rdword_of_val_mem SEGS); [exact VH | exact Rho]
    | apply (rdword_of_val_mem SEGS); [exact VS | exact Rst]
    | rewrite Hrf; exact (lh_aval_of_val _ _ _ 4 _ VR)
    | rewrite Hcd; apply lh_aval_mod32; exact (lh_aval_of_val _ _ _ 4 _ VC) ] ]
|]).
exfalso. clear - Hi. lhz.
Qed.

End e.
End f.
End d.
