(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_connect (plugin-hostd/fuzz_command, 0x8ad20, 160
   instructions), in the form of cgif_file_fuzzer's cgif_close walk (lib/A/ACh1.v..ACh8.v, AChc.v, instantiated
   in A/ACke.v at c8557374ad2e): the walk's parts, each proved over a stated state, composed here.
     - sup_connect_s3.v `scn_seg_a`: the entry 0x8ad20 to record()'s join 0x8adac (both arms; the spill arm
       through rec_calls_free);
     - sup_connect_s7.v `scn_seg_b`: the join 0x8adac (the stores c->fn, c->nargs) and the verb's null check
       to the first meeting point 0x8ade8;
     - sup_connect_s6.v `sb_seg1`: 0x8ade8 to 0x8ae50 (xstrdup(verb), the two stores, arg_line, the port_a
       null check);
     - sup_connect_s4.v `sb_seg2` and `sb_seg3`: to 0x8ae9c (xstrdup(port_a), the port_b null check), then
       xstrdup(port_b), the epilogue and `j answer`;
     - sup_connect_s5.v `scn_tail_ok`: answer's contract at its entry gives sup_connect's post.
   The interface (sup_connect_s0.v) states the statement's premises (`scn_pre`) and post (`scn_post`)
   conjunct for conjunct over the statement (passes 4 and 5 give the
   rounding-mode-0 premise in astack_pres's old place, the FP-existential post apost_baseF and the callees'
   contracts at every FP state), with the two ports left as the walk sees them (`option (list byte)`: the binary
   checks each for NULL, the statement hands `Some`). The only printf-reaching callee is answer, the tail jump,
   so the walk runs at the entry's FP state throughout and sup_connect_s5.v closes with answer's fx'. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable CmdSyms CmdList CmdPa CmdPaLib CmdBase CmdRep CmdObj CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_line_c answer_c sup_connect_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_connect_s0 sup_connect_s2 sup_connect_s3 sup_connect_s4 sup_connect_s5 sup_connect_s6 sup_connect_s7.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the callees' statements (sup_connect_c.v:75-78), at every FP state *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary facts of the walk hypotheses (cgif's names), which every walk carries *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the image facts and the program statics' writability (walk hypotheses IMG, PRW); the parts' named
   per-binary facts are CmdRecFacts.v's lemmas over these, applied in the theorem below *)
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis PRW : prog_rw SEGS B.

(* the walk's conclusion over every entry state gives the statement: `scn_post` is the statement's post
   word for word, and the statement's ports are the walk's `Some` arm *)
Definition SCN_A_stmt : Prop :=
forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (pv pl pa pb : Z) (verb : option (list byte))
  (line : list byte) (port_a port_b : option (list byte)) (R : rstate) (O : list (Z * Z)),
let t := snd (sup_connect_m R verb line port_a port_b) in
scn_pre B MT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_connect) regs mem md)
  (scn_post B MT ly S W regs mem md verb line port_a port_b R O t).
(* the statement's premises, premise for premise, give the walk's `scn_pre` (sup_connect_s0.v), with the
   two ports in the form the walk's null checks read them *)
Lemma scn_pre_of_spec : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch
  (pv pl pa pb : Z) (verb : option (list byte)) (line : list byte) (port_a port_b : list byte)
  (R : rstate) (O : list (Z * Z)),
let t := snd (sup_connect_m R verb line (Some port_a) (Some port_b)) in
afn_pre SEGS B SUP_CONNECT_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pv -> 0 <= pv < 2 ^ 64 -> getr regs 11 = w64 pl -> 0 <= pl < 2 ^ 64 ->
getr regs 12 = w64 pa -> 0 <= pa < 2 ^ 64 -> getr regs 13 = w64 pb -> 0 <= pb < 2 ^ 64 ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verb ->
(forall x, verb = Some x -> atail_vis SEGS W mem (pv + Z.of_nat (length x))) ->
(in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) /\
 Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O /\
 astr_atR (rdW W mem) pl line /\ Z.of_nat (length line) + 1 <= LMAX + 1) ->
(in_blockA (ablocks B ly S) pa (Z.of_nat (length port_a) + 1) /\
 Forall (fun qk => iv_apart pa (Z.of_nat (length port_a) + 1) (fst qk) (snd qk)) O /\
 astr_atR (rdW W mem) pa port_a /\ Z.of_nat (length port_a) + 1 <= LMAX + 1) ->
(in_blockA (ablocks B ly S) pb (Z.of_nat (length port_b) + 1) /\
 Forall (fun qk => iv_apart pb (Z.of_nat (length port_b) + 1) (fst qk) (snd qk)) O /\
 astr_atR (rdW W mem) pb port_b /\ Z.of_nat (length port_b) + 1 <= LMAX + 1) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_CONNECT R <= EV_MAX ->
blocks_bytes S + LIVE_SUP_CONNECT verb line (Some port_a) (Some port_b) t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_CONNECT MT R verb line (Some port_a) (Some port_b) t) ->
scn_pre B MT ly S W regs mem md ch pv pl pa pb verb line (Some port_a) (Some port_b) R O t.
Proof.
intros ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t.
intros HPRE HFRM HFR HROD HRO Hv Hv64 Hl Hl64 Ha Ha64 Hb Hb64 HV HVT HL HA HB2 HREP HEV HLIVE HMO.
exact (conj HPRE (conj HFRM (conj HFR (conj HROD (conj HRO (conj Hv (conj Hv64 (conj Hl (conj Hl64 (conj Ha
  (conj Ha64 (conj Hb (conj Hb64 (conj HV (conj HVT (conj HL (conj HA (conj HB2 (conj HREP (conj HEV
  (conj HLIVE HMO))))))))))))))))))))).
Qed.

Lemma tsup_connect_of_parts : SCN_A_stmt -> tsup_connect_spec B MT.
Proof.
intros HA. unfold tsup_connect_spec.
intros ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22.
exact (HA ly S W regs mem md ch pv pl pa pb verb line (Some port_a) (Some port_b) R O
  (scn_pre_of_spec ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O
     H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22)).
Qed.

(* sup_connect's statement: the parts, composed from answer's entry back to sup_connect's entry, with the parts'
   named per-binary facts discharged by CmdRecFacts.v (through the statements' rename map) *)
Theorem tsup_connect_spec_holds : tsup_connect_spec B MT.
Proof.
pose proof (cif_prog_img _ _ IMG) as F_PIMG.
pose proof (PROG_WRITABLE SEGS B LAWS HB PRW) as F_PW.
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG) as F_M3.
pose proof (cmd_tail_vis_at SEGS B LAWS HB IMG) as F_TAIL.
pose proof (cmd_ro_in_img SEGS B LAWS HB IMG) as F_ROIN.
pose proof (RRO SEGS B LAWS HB IMG) as F_RRO.
pose proof (RPG SEGS B LAWS HB IMG) as F_RPG.
(* CmdRecImg's cmd_heap_tail_vis covers the block's rounded size; the parts ask it inside the requested size *)
assert (F_HEAP : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e).
{ intros ly S W mem md p n e HAR Hin He.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
  apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md p n e HAR Hin). lia. }
exact (tsup_connect_of_parts
  (scn_seg_a B MT TREC_CALLS_FREE VOBJS HB LAWS TL MTL SIGP F_PIMG F_PW F_RPG
    (scn_seg_b B MT VOBJS HB LAWS F_PIMG F_PW F_RRO F_RPG
      (sb_seg1 B MT TXSTRDUP TARG_LINE VOBJS HB LAWS MTL SIGP F_PIMG F_PW F_M3 F_TAIL F_HEAP F_ROIN F_RRO F_RPG
        (sb_seg2 B MT TXSTRDUP VOBJS HB LAWS MTL SIGP F_PIMG F_PW F_M3 F_TAIL F_HEAP F_ROIN F_RRO F_RPG
          (sb_seg3 B MT TXSTRDUP VOBJS HB LAWS MTL SIGP F_PIMG F_PW F_M3 F_TAIL F_HEAP F_ROIN F_RRO F_RPG
            (scn_tail_ok B MT TANSWER HB LAWS MTL F_PIMG F_ROIN))))))).
Qed.

End e.
End f.
End d.

About tsup_connect_spec_holds.
Print Assumptions tsup_connect_spec_holds.
