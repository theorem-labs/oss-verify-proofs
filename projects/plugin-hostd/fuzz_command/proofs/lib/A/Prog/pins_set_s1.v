(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic states of pins_set's ASan walk (plugin-hostd/fuzz_command,
   0x8c7e8, 183 instructions), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed, the region and fact tables
   of cgif_close) and an earlier version of lib/A/Prog/RecBTemplate.v (the recorder globals as atoms). *)

(* pins_set (recorder.c:510-522) is block P (record(20), recorder.c:205-221), four argument blocks S (arg_s,
   the default "(null)" for uri / files / layout and "-" for verdict) and the tail TP (refuse test, mix_call,
   tail jump to answer_code) of the recorder-call walk template.

   Atoms above the 32 registers: 32 the shadow base, 33 g_rec.ncalls at the entry, 34 the slot c the call records
   into (g_rec.calls[ncalls] or record.spill), 35 / 36 g_rec.refuse / g_rec.code, 37 g_rec.state, 38 .. 47 the
   ten registers the prologue saves (ra, s0, s1, s2 .. s8). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas pins_set_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing offsets of the walk's segment ends (pins_set at AF_pins_set = 0x6304, image address 0x8c7e8) *)
Definition PS_ENTRY : Z := AF_pins_set.
Definition PS_JOIN : Z := AF_pins_set + 0x90.       (* 0x8c878: record()'s two arms meet *)
Definition PS_RET_RCF : Z := AF_pins_set + 0x70.    (* after rec_calls_free (0x8c858) *)
Definition PS_RET1 : Z := AF_pins_set + 0xd4.       (* after xstrdup #1 (0x8c8bc) *)
Definition PS_RET2 : Z := AF_pins_set + 0x124.      (* after xstrdup #2 (0x8c90c) *)
Definition PS_RET3 : Z := AF_pins_set + 0x170.      (* after xstrdup #3 (0x8c958) *)
Definition PS_RET4 : Z := AF_pins_set + 0x1bc.      (* after xstrdup #4 (0x8c9a4) *)
Definition PS_RET_MIX : Z := AF_pins_set + 0x208.   (* after mix_call (0x8c9f0) *)
Definition PS_FRAME : Z := 80.

(* the atoms *)
Definition PS_SB : nat := 32.
Definition PS_N : nat := 33.
Definition PS_C : nat := 34.
Definition PS_GREC : nat := A_OBJ 44.
Definition PS_SPILL : nat := A_OBJ 51.
Definition PS_NULL : nat := A_OBJ 52.
Definition PS_DASH : nat := A_OBJ 53.
Definition ps_Bx : sv := SOff PS_SB 0.
Definition ps_SH : list shent := [mkSHE PS_C 0 CALL_SIZE].
(* the saved registers, in the order the prologue stores them from sp + 72 down to sp + 0 *)
Definition ps_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24].
Definition ps_extra (regs : bvmap 5 word) (n c rf cd st : Z) : list word :=
map (Z_to_bv 64) [SB; n; c; rf; cd; st] ++ map (fun r => getr regs (Z_to_bv 5 r)) ps_saved.

(* the regions: the 80-byte frame, the two words of the shadow base, g_rec.ncalls, the slot, g_rec.refuse/code
   and g_rec.state *)
Definition ps_stack (d : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) d (d + 80) d (d + 80) cs.
Definition ps_ncalls (nv : sv) : YP09.region :=
YP09.mkRegion (Some PS_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 nv)].
Definition ps_slot (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some PS_C) 0 CALL_SIZE 0 CALL_SIZE cs.
Definition ps_rc : YP09.region :=
YP09.mkRegion (Some PS_GREC) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0)); YP09.mkChunk 4 (CVal 4 (SOff 36 0))].
Definition ps_state : YP09.region :=
YP09.mkRegion (Some PS_GREC) OFF_STATE (OFF_STATE + 8) OFF_STATE (OFF_STATE + 8)
  [YP09.mkChunk OFF_STATE (CVal 8 (SOff 37 0))].

(* the entry's regions; `nv` is the loaded call count: the atom PS_N on the arm that takes a slot of the table,
   the literal 16 on the arm that spills (with the atom's bounds the symbolic executor decides record()'s branch) *)
Definition ps_rs0 (nv : sv) : YP09.smem := [ps_stack (- 80) []; got_regionP; bcell_regionP PS_SB; ps_ncalls nv].

(* the program's own writable statics as the record's `as_prog_static B` lists them (base, length): RecBLemmas.v's
   recb_PG, which HB's ts_prog gives as TFIB_PROG_STATIC *)
Lemma ps_PG_tfib : TFIB_PROG_STATIC = recb_PG.
Proof. reflexivity. Qed.

Definition ps_facts (lo hi : Z) : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (PS_SB, mkAF SB SB 0); (PS_N, mkAF lo hi 0);
         (PS_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (PS_GREC, mkAF A_G_REC A_G_REC 3); (PS_SPILL, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].

(* the slot the inlined record() picks: ps_slot_of (pins_set_s2.v) *)
Definition ps_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + OFF_ANSWER /\ c mod 8 = 0) \/ c = A_REC_SPILL.

Lemma ps_slot_of_ok : forall n, 0 <= n <= 16 -> ps_slot_ok (ps_slot_of n).
Proof.
intros n Hn. unfold ps_slot_of. destruct (Z.eqb_spec n 16) as [E16 | E16]; [right; reflexivity | left].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER. split; [lia|]. split; [lia|].
replace (6174528 + 16 + 56 * n) with ((771818 + 7 * n) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma ps_slot_bounds : forall c, ps_slot_ok c -> A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0.
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *;
[split; [lia | exact H3] | split; [lia | reflexivity]].
Qed.

Lemma ps_pow4 : 2 ^ (8 * Z.of_N 4) = 2 ^ 32. Proof. reflexivity. Qed.
Lemma ps_pow8 : 2 ^ (8 * Z.of_N 8) = 2 ^ 64. Proof. reflexivity. Qed.

Lemma ps_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma ps_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

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
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
(* the program's statics (the names every recorder walk shares, RecBTemplate.v's forms): in the image, and present *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.

Lemma ps_grec_val : VAL PS_GREC = A_G_REC.
Proof. unfold PS_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma ps_spill_val : VAL PS_SPILL = A_REC_SPILL.
Proof. unfold PS_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma ps_null_val : VAL PS_NULL = 0x22480.
Proof. unfold PS_NULL. rewrite (VOBJS 52%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma ps_dash_val : VAL PS_DASH = 0x21d40.
Proof. unfold PS_DASH. rewrite (VOBJS 53%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma ps_got_val : VAL (A_OBJ 0) = 0xa63f0.
Proof. rewrite (VOBJS 0%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma ps_cell_val : VAL (A_OBJ 12) = 0xb10b8.
Proof. rewrite (VOBJS 12%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma ps_In_pair : forall (r : Z * Z) l, existsb (fun x => (fst x =? fst r) && (snd x =? snd r)) l = true -> In r l.
Proof.
intros [r1 r2] l. induction l as [|[x1 x2] l IH]; cbn; [discriminate|].
intros H. apply orb_true_iff in H as [H | H]; [left | right; exact (IH H)].
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. reflexivity.
Qed.

(* g_rec and record.spill lie in zero-shadow ranges of the record (AF0m.v Tfib_zero_shadow) *)
Lemma ps_addressable_grec : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> 0xada00 <= a -> a + n <= 0x5e3b00 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) a n HAR);
  [apply ps_In_pair; vm_compute; reflexivity | reflexivity | reflexivity | cbn [fst]; exact Hlo | cbn [fst snd]; lia].
Qed.

Lemma ps_addressable_spill : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> range_addressable (rdW W mem) SHADOW_OFF A_REC_SPILL SC_SIZE.
Proof.
intros ly S W mem md HAR.
apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) A_REC_SPILL SC_SIZE HAR);
  [apply ps_In_pair; vm_compute; reflexivity | reflexivity | reflexivity | cbn [fst]; reflexivity | cbn [fst snd]; reflexivity].
Qed.

Lemma ps_slot_addressable : forall ly S (W : world SEGS) mem md c,
AR SEGS B ly S W mem md -> ps_slot_ok c -> range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR [(H1 & H2 & H3) | ->].
- apply (ps_addressable_grec ly S W mem md); [exact HAR | |]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *; lia.
- exact (ps_addressable_spill ly S W mem md HAR).
Qed.

Lemma ps_sh_ok : forall ly S (W : world SEGS) mem md E c,
AR SEGS B ly S W mem md -> ew E PS_SB = Z_to_bv 64 SB -> ew E PS_C = Z_to_bv 64 c -> ps_slot_ok c ->
sh_ok SEGS ps_Bx ps_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR ESB EC Hc.
destruct (ps_slot_bounds c Hc) as [Hcb Hc8].
unfold sh_ok, ps_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E ps_Bx PS_C c CALL_SIZE c 0 CALL_SIZE).
- exact (ps_slot_addressable ly S W mem md c HAR Hc).
- unfold ps_Bx. apply ps_U_atom; [exact ESB | cbv [SB SHADOW_OFF]; lia].
- apply ps_U_atom; [exact EC | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

(* the entry state: every register is its own atom *)
Definition ps_E0 (regs : bvmap 5 word) (n c rf cd st : Z) : env := Eimg (Ereg regs (ps_extra regs n c rf cd st)).

Lemma ps_E0_extra : forall regs n c rf cd st,
ew (ps_E0 regs n c rf cd st) PS_SB = Z_to_bv 64 SB /\ ew (ps_E0 regs n c rf cd st) PS_N = Z_to_bv 64 n /\
ew (ps_E0 regs n c rf cd st) PS_C = Z_to_bv 64 c /\ ew (ps_E0 regs n c rf cd st) 35%nat = Z_to_bv 64 rf /\
ew (ps_E0 regs n c rf cd st) 36%nat = Z_to_bv 64 cd /\ ew (ps_E0 regs n c rf cd st) 37%nat = Z_to_bv 64 st.
Proof.
intros. unfold ps_E0.
rewrite !Eimg_low by (unfold PS_SB, PS_N, PS_C, A_TEXT; lia).
change PS_SB with (32 + 0)%nat. change PS_N with (32 + 1)%nat. change PS_C with (32 + 2)%nat.
change 35%nat with (32 + 3)%nat. change 36%nat with (32 + 4)%nat. change 37%nat with (32 + 5)%nat.
rewrite !ew_Ereg_extra. cbn [ps_extra nth map app]. repeat split.
Qed.

Lemma ps_E0_reg : forall regs n c rf cd st k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (ps_E0 regs n c rf cd st) k = getr regs r.
Proof.
intros regs n c rf cd st k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
unfold ps_E0. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.

Lemma ps_entry_seed : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) n c rf cd st nv lo hi,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> 0 <= n <= 16 -> c = ps_slot_of n -> lo <= n <= hi ->
(forall a, spZ regs - 80 <= a < spZ regs -> apresent (w_H W) mem a) ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
sv_denot (ps_E0 regs n c rf cd st) nv = Z_to_bv 64 n ->
st_ok_pi SEGS VAL (ps_E0 regs n c rf cd st) (mkSS PS_ENTRY sr_atoms (ps_rs0 nv) None (ps_facts lo hi))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PS_ENTRY)) mem (seg_rom SEGS)))
/\ sh_ok SEGS ps_Bx ps_SH (ps_E0 regs n c rf cd st) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs n c rf cd st nv lo hi HAR Hsp Hsp16 Hn Hc Hlh Hpres HNC HNV.
set (E := ps_E0 regs n c rf cd st).
assert (HEI : img_env VAL A_LIM E) by (unfold E, ps_E0; apply Eimg_env).
destruct (ps_E0_extra regs n c rf cd st) as (ESB & EN & EC & _). fold E in ESB, EN, EC.
assert (E2 : ew E 2 = getr regs 2) by (apply ps_E0_reg; reflexivity).
pose proof (ps_slot_of_ok n Hn) as Hcok. rewrite <- Hc in Hcok.
destruct (ps_slot_bounds c Hcok) as [Hcb Hc8].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pal_got_cell B TL) as Hgc.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
assert (EG : ew E PS_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E PS_GREC HEI ltac:(unfold PS_GREC, A_OBJ, A_TEXT, A_LIM; lia)), ps_grec_val; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [| exact (ps_sh_ok ly S W mem md E c HAR ESB EC Hcok)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- unfold E, ps_E0. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ps_rs0, ps_stack, got_regionP, bcell_regionP, ps_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 2%nat (spZ regs) E2') by lia. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite ps_pow8; pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 ps_Bx SHADOW_OFF);
    [cbn [sv_denot ps_Bx]; rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite ps_pow8; cbv [SHADOW_OFF]; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB PS_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
      apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE, A_G_REC in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 nv n);
    [exact HNV | rewrite ps_pow4; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold ps_rs0, ps_stack, got_regionP, bcell_regionP, ps_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB PS_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  rewrite (VB 2%nat (spZ regs) E2') by lia.
  rewrite ps_got_val, ps_cell_val.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_NCALLS in *.
  repeat split; lia.
- unfold facts_ok, ps_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
  + apply (ps_afact E 2%nat (spZ regs)); [exact E2' | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
  + apply (ps_afact E PS_SB SB); [exact ESB | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (ps_afact E PS_N n); [exact EN | lia | exact Hlh | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (ps_afact E PS_C c); [exact EC | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb
    | change (2 ^ 3) with 8; exact Hc8 | lia].
  + apply (ps_afact E PS_GREC A_G_REC); [exact EG | unfold A_G_REC; lia | lia | reflexivity | lia].
  + assert (ES : ew E PS_SPILL = Z_to_bv 64 A_REC_SPILL)
      by (rewrite (img_env_atomP E PS_SPILL HEI ltac:(unfold PS_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), ps_spill_val; reflexivity).
    apply (ps_afact E PS_SPILL A_REC_SPILL); [exact ES | unfold A_REC_SPILL; lia | lia | reflexivity | lia].
Qed.

End e.
End f.
End d.
