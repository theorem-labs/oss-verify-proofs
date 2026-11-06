(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic states and seeds of lv2_refusals_forget's ASan walk
   (plugin-hostd/fuzz_command, 0x8d278), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seed, the region and
   fact tables of cgif_close's walk) at c8557374ad2e, and the entry seed of the recorder-call template
   (lib/A/Prog/RecBTemplate.v, lib/A/Prog/sup_worker_list.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import lv2_refusals_forget_s2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the atoms the walk adds above the 32 registers: the shadow base, g_rec.ncalls at the entry, the slot record()
   picks, g_rec.state at the entry, the string handed to xstrdup, and (from the join on) the seven callee-saved
   registers the prologue stores *)
Definition L_SB : nat := 32.
Definition L_N : nat := 33.
Definition L_C : nat := 34.
Definition L_H : nat := 35.
Definition L_S : nat := 36.
Definition L_GREC : nat := A_OBJ 44.
Definition L_SPILL : nat := A_OBJ 51.
Definition L_STAR : nat := A_OBJ 78.
Definition L_Bx : sv := SOff L_SB 0.
Definition L_SH : list shent := [mkSHE L_C 0 CALL_SIZE].
(* the listing offsets of the walk's stops *)
Definition L_ENTRY : Z := AF_lv2_refusals_forget.           (* 0x8d278 *)
Definition L_RCF_RET : Z := AF_lv2_refusals_forget + 0x58.  (* 0x8d2d0, after rec_calls_free *)
Definition L_JOIN : Z := AF_lv2_refusals_forget + 0x78.     (* 0x8d2f0, the two arms of record() meet *)
Definition L_ARG : Z := AF_lv2_refusals_forget + 0xb4.      (* 0x8d32c, a0 := the string *)
Definition L_XS_RET : Z := AF_lv2_refusals_forget + 0xbc.   (* 0x8d334, after xstrdup *)
Definition L_MIX_RET : Z := AF_lv2_refusals_forget + 0x100. (* 0x8d378, after mix_call *)
(* the program's own writable statics as as_prog_static lists them: base and length *)
Definition lrf_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the effective argument and its address: uri, or the literal "*" (.str.21, 0x21fa0) when uri is NULL *)
Definition lrf_star : list byte := bstr "*"%string.
Definition lrf_x (uri : option (list byte)) : list byte := darg uri lrf_star.
Definition lrf_s (pu : Z) : Z := if pu =? 0 then 0x21fa0 else pu.

(* ---- the entry segment: prologue, the shadow base, g_rec.ncalls and its test ---------------------------- *)
Definition lrf_stack (d : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) d 0 d 0 cs.
Definition lrf_ncalls : YP09.region :=
YP09.mkRegion (Some L_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff L_N 0))].
Definition lrf_rs0 : smem := [lrf_stack (-64) []; got_regionP; bcell_regionP L_SB; lrf_ncalls].
(* the call count's atom carries the bounds of record()'s arm: [0, 15] for the table, [16, 16] for record.spill,
   so the executor settles `bne ncalls, 16` itself *)
Definition lrf_facts0 (lo hi : Z) : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (L_SB, mkAF SB SB 0); (L_N, mkAF lo hi 0);
         (L_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3); (L_GREC, mkAF A_G_REC A_G_REC 3)] [] [].
Definition lrf_ss0 (lo hi : Z) : sstate := mkSS L_ENTRY sr_atoms lrf_rs0 None (lrf_facts0 lo hi).
Definition lrf_extra0 (n c h s : Z) : list word := map (Z_to_bv 64) [SB; n; c; h; s].

(* ---- the join: from 0x8d2f0 on, the slot is the atom L_C, s3 is g_rec, s4 the shadow base --------------- *)
Definition lrf_saved : list Z := [1; 8; 9; 18; 19; 20; 21].
Definition lrf_extra1 (regs0 : bvmap 5 word) (n c h s : Z) : list word :=
lrf_extra0 n c h s ++ map (fun r => getr regs0 (Z_to_bv 5 r)) lrf_saved.
(* the frame the prologue wrote: ra at sp+56, s0 at +48, s1 +40, s2 +32, s3 +24, s4 +16, s5 +8 (atoms 37..43) *)
Definition lrf_frame1 : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0
  (map (fun j => YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (37 + j) 0))) (seq 0 7)).
Definition lrf_state : YP09.region :=
YP09.mkRegion (Some L_GREC) OFF_STATE (OFF_STATE + 8) OFF_STATE (OFF_STATE + 8)
  [YP09.mkChunk OFF_STATE (CVal 8 (SOff L_H 0))].
Definition lrf_slot : YP09.region := YP09.mkRegion (Some L_C) 0 CALL_SIZE 0 CALL_SIZE [].
Definition lrf_rs1 : smem := [lrf_frame1; got_regionP; bcell_regionP L_SB; lrf_state; lrf_slot].
Definition lrf_facts1 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (L_SB, mkAF SB SB 0);
         (L_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3); (L_GREC, mkAF A_G_REC A_G_REC 3)] [] [].
Definition lrf_regs1 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set sr_atoms 8 (SOff L_C 0)) 19 (SOff L_GREC 0)) 20 (SOff L_SB 0).
Definition lrf_ss1 : sstate := mkSS L_JOIN lrf_regs1 lrf_rs1 None lrf_facts1.
(* the call of xstrdup (0x8d330): both arms of `s := s ? s : "*"` meet here, with s1 = a0 = the string *)
Definition L_XS_CALL : Z := AF_lv2_refusals_forget + 0xb8.
Definition lrf_K1 : nat := Eval vm_compute in run_K A_LIM L_Bx L_SH lrf_ss1.
Definition lrf_ssb : sstate := Eval vm_compute in
  sh_ss (fst (sym_runN_pi_tok cmd_tpi cmd_tw lrf_K1 L_Bx Bspan L_SH FUEL lrf_ss1)).
Definition lrf_ss2 : sstate := Eval vm_compute in
  let st := sh_ss (fst (sym_run_toN_pi_tok cmd_tpi cmd_tw lrf_K1 L_Bx Bspan L_SH FUEL L_XS_CALL
    (add_cond lrf_ssb (mkAC BC_NE (SOff 9 0) (SLit 0))))) in
  mkSS (ss_pc st) (sr_set (sr_set (ss_regs st) 9 (SOff L_S 0)) 10 (SOff L_S 0)) (ss_mem st) None lrf_facts1.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Lemma lrf_grec_val : VAL L_GREC = A_G_REC.
Proof. unfold L_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma lrf_spill_val : VAL L_SPILL = A_REC_SPILL.
Proof. unfold L_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma lrf_star_val : VAL L_STAR = 0x21fa0.
Proof. unfold L_STAR. rewrite (VOBJS 78%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma lrf_got_val : VAL (A_OBJ 0) = 0xa63f0.
Proof. rewrite (VOBJS 0%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma lrf_cell_val : VAL (A_OBJ 12) = 0xb10b8.
Proof. rewrite (VOBJS 12%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma lrf_inFP_grec : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP (lrf_FP O) a.
Proof. intros O a Ha. exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha]. Qed.
Lemma lrf_inFP_spill : forall O a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP (lrf_FP O) a.
Proof.
intros O a Ha. exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.
(* a write of the walk to g_rec or record.spill: the footprint names it, and it is a program static of the image
   (awr_byte's program-static disjunct, lib/Reusable/YCbq.v:497) *)
Lemma lrf_awr_PG : forall STK sp0 O bl0 blc fr0 ly own a,
inFP (lrf_FP O) a -> Exists (in_zr a) recb_PG ->
awr_byte SEGS B STK sp0 (lrf_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Hfp HPG. right; right; right; right. left.
split; [exact Hfp|]. split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)].
Qed.
Lemma lrf_awr_cons_grec : forall E r rs STK sp0 O bl0 blc fr0 ly own,
YP09.r_base r = Some L_GREC -> img_env VAL A_LIM E ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= REC_SIZE ->
awr_ok SEGS B E rs STK sp0 (lrf_FP O) bl0 blc fr0 ly own -> awr_ok SEGS B E (r :: rs) STK sp0 (lrf_FP O) bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 O bl0 blc fr0 ly own Hb HEI Hlo Hhi H.
eapply awr_ok_cons_gen with (n := L_GREC) (b := A_G_REC); [exact Hb | | | exact H].
- rewrite (HEI L_GREC ltac:(unfold L_GREC, A_OBJ, A_TEXT, A_LIM; lia)). exact lrf_grec_val.
- intros a Ha. assert (Ha' : A_G_REC <= a < A_G_REC + REC_SIZE) by lia.
  exact (lrf_awr_PG STK sp0 O bl0 blc fr0 ly own a (lrf_inFP_grec O a Ha') (recb_grec_in a Ha')).
Qed.


(* the slot: an entry of g_rec's call table or record.spill, 8-aligned *)
Definition lrf_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + OFF_ANSWER /\ c mod 8 = 0) \/ c = A_REC_SPILL.
Lemma lrf_c_ok : forall n, 0 <= n <= 16 -> lrf_slot_ok (lrf_c n).
Proof.
intros n Hn. unfold lrf_c. destruct (Z.eqb_spec n 16) as [E16 | E16]; [right; reflexivity | left].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER. split; [lia|]. split; [lia|].
replace (6174528 + 16 + 56 * n) with ((771818 + 7 * n) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma lrf_slot_bounds : forall c, lrf_slot_ok c -> A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0.
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *;
[split; [lia | exact H3] | split; [lia | reflexivity]].
Qed.
Lemma lrf_slot_PG : forall c a, lrf_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a [(H1 & H2 & _) | ->] Ha; [apply recb_grec_in | apply recb_spill_in];
unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia.
Qed.
Lemma lrf_slot_FP : forall O c a, lrf_slot_ok c -> c <= a < c + CALL_SIZE -> inFP (lrf_FP O) a.
Proof.
intros O c a [(H1 & H2 & _) | ->] Ha; [apply lrf_inFP_grec | apply lrf_inFP_spill];
unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia.
Qed.
Lemma lrf_awr_cons_slot : forall E r rs STK sp0 O bl0 blc fr0 ly own c,
YP09.r_base r = Some L_C -> ew E L_C = Z_to_bv 64 c -> lrf_slot_ok c ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= CALL_SIZE ->
awr_ok SEGS B E rs STK sp0 (lrf_FP O) bl0 blc fr0 ly own -> awr_ok SEGS B E (r :: rs) STK sp0 (lrf_FP O) bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 O bl0 blc fr0 ly own c Hb EC Hc Hlo Hhi H.
destruct (lrf_slot_bounds c Hc) as [Hcb _].
eapply awr_ok_cons_gen with (n := L_C) (b := c); [exact Hb | | | exact H].
- rewrite EC. apply unsigned_lit_small. unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
- intros a Ha. assert (Ha' : c <= a < c + CALL_SIZE) by lia.
  exact (lrf_awr_PG STK sp0 O bl0 blc fr0 ly own a (lrf_slot_FP O c a Hc Ha') (lrf_slot_PG c a Hc Ha')).
Qed.
(* a symbolic state with other register forms of the same values and fewer facts *)
Lemma lrf_st_ok_canon : forall E ss ms sr G,
st_ok_pi SEGS VAL E ss ms -> (forall r, sv_denot E (sr_get sr r) = sv_denot E (sr_get (ss_regs ss) r)) -> facts_ok E G ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) sr (ss_mem ss) (ss_resv ss) G) ms.
Proof.
intros E [pc sr0 fr0 m0 rv0 G0] ms sr G (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr HG.
unfold abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [|split; [exact H8 | exact HG]].
intros r. rewrite (H7 r). symmetry. apply Hr.
Qed.
Lemma lrf_facts_atoms : forall E at0 cs al, facts_ok E (mkFacts at0 cs al) -> facts_ok E (mkFacts at0 [] []).
Proof. intros E at0 cs al [Ha _]. split; [exact Ha | split; exact I]. Qed.
(* both arms of `s ? s : "*"` reach the call of xstrdup in the state lrf_ss2, whose s1 and a0 are the atom of the
   string *)
Lemma lrf_canon2 : forall E ss ms v,
st_ok_pi SEGS VAL E ss ms ->
ss_pc ss = ss_pc lrf_ss2 -> ss_mem ss = ss_mem lrf_ss2 -> ss_resv ss = None ->
f_atoms (ss_facts ss) = f_atoms lrf_facts1 ->
forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get (ss_regs lrf_ss2) r) ||
   (sv_eqb (sr_get (ss_regs ss) r) v && sv_eqb (sr_get (ss_regs lrf_ss2) r) (SOff L_S 0))) all_regs = true ->
sv_denot E v = sv_denot E (SOff L_S 0) ->
st_ok_pi SEGS VAL E lrf_ss2 ms.
Proof.
intros E [pc sr0 fr0 m0 rv0 G0] ms v HS Hpc Hm Hrv Hat Hb Hv.
cbn [ss_pc ss_mem ss_resv ss_facts ss_regs] in Hpc, Hm, Hrv, Hat, Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & H9). unfold abs_ss, setpc in H9. cbn [ss_facts] in H9.
assert (HG : facts_ok E lrf_facts1).
{ destruct G0 as [at0 cs al]. cbn [f_atoms] in Hat. subst at0. exact (lrf_facts_atoms E _ cs al H9). }
assert (Hr : forall r, sv_denot E (sr_get (ss_regs lrf_ss2) r) = sv_denot E (sr_get sr0 r)).
{ intros r. pose proof (all_regs_in r) as Hin.
  pose proof (proj1 (forallb_forall _ _) Hb r Hin) as Hbr. cbv beta in Hbr.
  apply orb_true_iff in Hbr as [H1 | H2].
  - rewrite (sv_eqb_eq _ _ H1). reflexivity.
  - apply andb_prop in H2 as [H2 H3]. rewrite (sv_eqb_eq _ _ H2), (sv_eqb_eq _ _ H3). symmetry. exact Hv. }
pose proof (lrf_st_ok_canon E _ ms (ss_regs lrf_ss2) lrf_facts1 HS Hr HG) as H.
cbn [ss_pc ss_mem ss_resv] in H. rewrite Hpc, Hm, Hrv in H.
exact H.
Qed.

Lemma lrf_in_of_b : forall (x : Z * Z) l, existsb (fun r => (fst r =? fst x) && (snd r =? snd x)) l = true -> In x l.
Proof.
intros [x1 x2] l H. apply existsb_exists in H as ([y1 y2] & Hy & E). cbn [fst snd] in E.
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exact Hy.
Qed.
(* the record's zero-shadow ranges that hold g_rec and record.spill (lib/A/AF0m.v Tfib_zero_shadow) *)
Lemma lrf_zsh_grec : In (0xada00, 0x5e3b00 - 0xada00) Tfib_zero_shadow.
Proof. apply lrf_in_of_b. vm_compute. reflexivity. Qed.
Lemma lrf_zsh_spill : In (0x5e3be0, 0x5e3c18 - 0x5e3be0) Tfib_zero_shadow.
Proof. apply lrf_in_of_b. vm_compute. reflexivity. Qed.
Lemma lrf_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> lrf_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR [(H1 & H2 & _) | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md _ c CALL_SIZE HAR lrf_zsh_grec);
  [reflexivity | reflexivity | cbn [fst]; unfold A_G_REC, OFF_CALLS in H1; lia
  | cbn [fst snd]; unfold A_G_REC, OFF_ANSWER, CALL_SIZE in *; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md _ A_REC_SPILL CALL_SIZE HAR lrf_zsh_spill);
  [reflexivity | reflexivity | cbn [fst]; unfold A_REC_SPILL; lia | cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE; lia].
Qed.
Lemma lrf_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.
Lemma lrf_sh_ok : forall ly S (W : world SEGS) mem md E c,
AR SEGS B ly S W mem md -> ew E L_SB = Z_to_bv 64 SB -> ew E L_C = Z_to_bv 64 c -> lrf_slot_ok c ->
sh_ok SEGS L_Bx L_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR ESB EC Hc.
destruct (lrf_slot_bounds c Hc) as [Hcb Hc8].
unfold sh_ok, L_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E L_Bx L_C c CALL_SIZE c 0 CALL_SIZE).
- exact (lrf_slot_addressable ly S W mem md c HAR Hc).
- unfold L_Bx. apply lrf_U_atom; [exact ESB | cbv [SB SHADOW_OFF]; lia].
- apply lrf_U_atom; [exact EC | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

Lemma lrf_pow8 : 2 ^ (8 * Z.of_N 8) = 2 ^ 64. Proof. reflexivity. Qed.
Lemma lrf_pow4 : 2 ^ (8 * Z.of_N 4) = 2 ^ 32. Proof. reflexivity. Qed.

(* the entry state: every register its own atom; the frame below sp, the GOT word and the shadow cell that give
   the shadow base, and g_rec.ncalls *)
Lemma lrf_seed0 : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) n c h s lo hi,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - 64 <= a < spZ regs -> apresent (w_H W) mem a) ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= lo -> lo <= n <= hi -> hi <= 16 -> lrf_slot_ok c ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lrf_extra0 n c h s))) (lrf_ss0 lo hi)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_ENTRY)) mem (seg_rom SEGS)))
/\ sh_ok SEGS L_Bx L_SH (Eimg (Ereg regs (lrf_extra0 n c h s))) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs n c h s lo hi HAR Hsp Hsp16 Hpres HNC Hlo Hn Hhi Hc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs (lrf_extra0 n c h s))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (lrf_extra0 n c h s) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = getr regs 2) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (ESB : ew E L_SB = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (EN : ew E L_N = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (EC : ew E L_C = Z_to_bv 64 c) by exact (EX 2%nat ltac:(lia)).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
assert (EG : ew E L_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E L_GREC HEI ltac:(unfold L_GREC, A_OBJ, A_TEXT, A_LIM; lia)), lrf_grec_val; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split; [| exact (lrf_sh_ok ly S W mem md E c HAR ESB EC Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- unfold E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold lrf_rs0, lrf_stack, got_regionP, bcell_regionP, lrf_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + pose proof (pa_val_range (A_OBJ 0)) as HV0.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia.
    split; [lia|]. split; [rewrite lrf_got_val; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite lrf_pow8; pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + pose proof (pa_val_range (A_OBJ 12)) as HV12.
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia.
    split; [lia|]. split; [rewrite lrf_cell_val; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 L_Bx SHADOW_OFF);
    [cbn [sv_denot L_Bx]; rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite lrf_pow8; cbv [SHADOW_OFF]; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB L_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
      apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE, A_G_REC in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff L_N 0) n);
    [cbn [sv_denot]; rewrite EN, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite lrf_pow4; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold lrf_rs0, lrf_stack, got_regionP, bcell_regionP, lrf_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB L_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite Usp, lrf_got_val, lrf_cell_val.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_NCALLS in *.
  repeat split; lia.
- destruct (lrf_slot_bounds c Hc) as [Hcb Hc8].
  split; [|split; [exact I | exact I]].
  cbn [lrf_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, ESB, EN, EC, EG, !unsigned_lit_small by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia].
Qed.

(* the registers at the join, as the seed states them: s0 the slot, s3 g_rec, s4 the shadow base *)
Lemma lrf_regs1_ok : forall (regs1 : bvmap 5 word) extra c,
getr regs1 8 = w64 c -> getr regs1 19 = w64 A_G_REC -> getr regs1 20 = w64 SB ->
ew (Eimg (Ereg regs1 extra)) L_C = Z_to_bv 64 c -> ew (Eimg (Ereg regs1 extra)) L_SB = Z_to_bv 64 SB ->
regs_ok (Eimg (Ereg regs1 extra)) lrf_regs1 regs1.
Proof.
intros regs1 extra c R8 R19 R20 EC ESB.
set (E := Eimg (Ereg regs1 extra)) in *.
change L_C with 34%nat in EC. change L_SB with 32%nat in ESB.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EG : ew E L_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E L_GREC HEI ltac:(unfold L_GREC, A_OBJ, A_TEXT, A_LIM; lia)), lrf_grec_val; reflexivity).
change L_GREC with 285%nat in EG.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
      let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
          | rewrite EC; exact R8 | rewrite EG; exact R19 | rewrite ESB; exact R20 ]
  | ]); try (destruct Hr; fail).
Qed.

Lemma lrf_seed1 : forall ly S (W : world SEGS) mem md (regs0 regs1 : bvmap 5 word) n c h s,
AR SEGS B ly S W mem md ->
2 ^ 46 + 64 <= spZ regs0 <= 2 ^ 47 -> spZ regs0 mod 16 = 0 ->
spZ regs1 = spZ regs0 - 64 -> getr regs1 8 = w64 c -> getr regs1 19 = w64 A_G_REC -> getr regs1 20 = w64 SB ->
(forall j r, nth_error lrf_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r)))) ->
aval_mem (rdW W mem) (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 -> lrf_slot_ok c ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (lrf_extra1 regs0 n c h s))) lrf_ss1
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + L_JOIN)) mem (seg_rom SEGS)))
/\ sh_ok SEGS L_Bx L_SH (Eimg (Ereg regs1 (lrf_extra1 regs0 n c h s))) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs0 regs1 n c h s HAR Hsp Hsp16 Hsp1 R8 R19 R20 HFR HST Hh Hc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (lrf_extra1 regs0 n c h s))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EX : forall j, (j < 12)%nat -> ew E (32 + j) = nth j (lrf_extra1 regs0 n c h s) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = getr regs1 2) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (ESB : ew E L_SB = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (EC : ew E L_C = Z_to_bv 64 c) by exact (EX 2%nat ltac:(lia)).
assert (EH : ew E L_H = Z_to_bv 64 h) by exact (EX 3%nat ltac:(lia)).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
assert (EG : ew E L_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E L_GREC HEI ltac:(unfold L_GREC, A_OBJ, A_TEXT, A_LIM; lia)), lrf_grec_val; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 64) by (rewrite E2; exact Hsp1).
destruct (lrf_slot_bounds c Hc) as [Hcb Hc8].
split; [| exact (lrf_sh_ok ly S W mem md E c HAR ESB EC Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- unfold E. apply (lrf_regs1_ok regs1 _ c R8 R19 R20 EC ESB).
- vm_compute. reflexivity.
- unfold lrf_rs1, lrf_frame1, got_regionP, bcell_regionP, lrf_state, lrf_slot.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?m 0))) =>
    let j := eval compute in (m - 37)%nat in
    let j5 := eval compute in (m - 32)%nat in
    let r := eval compute in (nth j lrf_saved 0) in
    let Ej := fresh "Ej" in
    pose proof (EX j5 ltac:(lia)) as Ej; cbn [Nat.add lrf_extra1 lrf_extra0 lrf_saved map app nth] in Ej;
    apply (chunk_ok_val SEGS E _ (spZ regs0 - 64) off 8 (SOff m 0) (bv_unsigned (getr regs0 (Z_to_bv 5 r))));
    [ cbn [sv_denot]; rewrite Z.add_0_r, Ej, Z_to_bv_bv_unsigned; reflexivity
    | rewrite lrf_pow8; pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 r))) as HR;
      change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
    | cbn; lia
    | replace (spZ regs0 - 64 + off) with (spZ regs0 - 8 - 8 * Z.of_nat j) by (cbn; lia);
      exact (HFR j r eq_refl) ]; clear Ej end.
  + pose proof (pa_val_range (A_OBJ 0)) as HV0.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia.
    split; [lia|]. split; [rewrite lrf_got_val; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite lrf_pow8; pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + pose proof (pa_val_range (A_OBJ 12)) as HV12.
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia.
    split; [lia|]. split; [rewrite lrf_cell_val; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 L_Bx SHADOW_OFF);
    [cbn [sv_denot L_Bx]; rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite lrf_pow8; cbv [SHADOW_OFF]; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB L_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_STATE; lia|]. split; [unfold A_G_REC, OFF_STATE; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
      apply recb_grec_in. unfold OFF_STATE, REC_SIZE, A_G_REC in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_STATE 8 (SOff L_H 0) h);
    [cbn [sv_denot]; rewrite EH, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite lrf_pow8; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_STATE) 8%nat h HST).
  + rewrite (VB L_C c EC) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
    split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold A_REC_SPILL, CALL_SIZE in *; lia|].
    split; [|constructor].
    intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
    apply (lrf_slot_PG c); [exact Hc | lia].
- apply pairwise_disjoint_of_extents.
  unfold lrf_rs1, lrf_frame1, got_regionP, bcell_regionP, lrf_state, lrf_slot, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB L_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  rewrite (VB L_C c EC) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  cbn [base_val]. rewrite Usp, lrf_got_val, lrf_cell_val.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct Hc as [(Hc1 & Hc2 & _) | ->];
  unfold A_G_REC, A_REC_SPILL, OFF_STATE, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *;
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [lrf_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, ESB, EC, EG, !unsigned_lit_small by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *.
  repeat match goal with |- _ /\ _ => split end; try first [exact I | reflexivity | lia].
  all: first [ lia
             | replace (spZ regs0 - 64) with (spZ regs0 + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hsp16 ].
Qed.
End e.
End f.
End d.
