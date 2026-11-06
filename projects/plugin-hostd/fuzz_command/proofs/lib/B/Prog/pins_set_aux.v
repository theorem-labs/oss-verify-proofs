(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the facts of pins_set's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, tpins_set_spec of lib/B/Prog/pins_set_c.v, statement from a Theorem Labs lane 917ca7ac6b1) that need
   none of its callees' statements: the pcs and call targets of the B code, the default verdict "-" (0x21d80, the
   listing's object A_OBJ 52) as an argument string, the heap arguments, the recorder's scalars and held answer, and
   the model's two arms. After the ASan walk lib/A/Prog/pins_set.v and pins_set_s2/s3/s7/s10/s11.v
   (a working branch 3cc8391594b: ps_blk_arg, ps_O_facts, pt_same_start, ps_rec_record_scalars and the refuse /
   mix arms of ps_seg_x4) and lib/A/Prog/RecBLemmas.v there (acall_at_in, lay_blocks_in).

   B code (fuzz_command.asan-ubsan, sha256 658cefbe806b535ba1fbe5a37c8efe02099fc39c326f300e9b1c969d479df401,
   .symtab pins_set = 0x8c938, size 192 = 48 instructions; listing lib/B/Prog/CmdList.v:6481-6528):
     0x8c938 addi sp,sp,-48 ; sd ra,s0,s1,s2,s3,s4 ; mv s1,a3 ; mv s2,a2 ; mv s3,a1 ; mv s4,a0 ; li a0,20
     0x8c968 jal record                     record(REC 20), the slot in a0 -> s0
     0x8c974 / 0x8c980 / 0x8c98c jal arg_s  arg_s(slot, uri), arg_s(slot, files), arg_s(slot, layout)
     0x8c990 bnez s1 -> 0x8c99c ; 0x8c994 auipc a0 / addi s1 (A_OBJ 52 = 0x21d80 "-")
     0x8c9a4 jal arg_s                      arg_s(slot, verdict or "-")
     0x8c9a8 auipc a0 / addi s1 (A_OBJ 44 = g_rec 0x5e32c0) ; lw a0,0(s1) (g_rec.refuse)
     0x8c9b4 beqz a0 -> 0x8c9c0 ; lw a0,4(s1) (g_rec.code) ; j 0x8c9d8
     0x8c9c0 ld a0,0x3b0(s1) (g_rec.state) ; mv a1,s0 ; 0x8c9c8 jal mix_call ; mv a1,a0 ; li a0,0 ;
     0x8c9d4 sd a1,0x3b0(s1)
     0x8c9d8 ld ra,s0..s4 ; addi sp,sp,48 ; 0x8c9f4 j answer_code   answer_code(code) at the entry sp
   No `jal __asan_report_*`, no unimp / ebreak: 0 report and 0 UBSan trap edges. The two conditional branches are
   data branches: 0x8c990 on the verdict pointer (psb_verdict_null), 0x8c9b4 on g_rec.refuse (psb_scalars and
   psb_model_refuse / psb_model_mix). Every load and store through an auipc pair goes through s1 = the A_OBJ value
   (VOBJS), none through an A_HI value, so the walk needs no cmd_val_his. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable CmdSyms CmdList CmdAddr CmdPa CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* --- the B code: frame, pcs, listing entries, callees ------------------------------------------------------ *)
Definition PSB_FRAME : Z := 48.
Definition PSB_CALL_RECORD : Z := AF_pins_set + 0x30.  (* jal record (0x8c968) *)
Definition PSB_RET_RECORD : Z := AF_pins_set + 0x34.   (* mv s0,a0 (0x8c96c) *)
Definition PSB_RET_ARG1 : Z := AF_pins_set + 0x40.     (* after arg_s(slot, uri) (0x8c978) *)
Definition PSB_RET_ARG2 : Z := AF_pins_set + 0x4c.     (* after arg_s(slot, files) (0x8c984) *)
Definition PSB_RET_ARG3 : Z := AF_pins_set + 0x58.     (* after arg_s(slot, layout): bnez s1 (0x8c990) *)
Definition PSB_DASH : Z := AF_pins_set + 0x5c.         (* auipc a0 of "-" (0x8c994) *)
Definition PSB_JOIN4 : Z := AF_pins_set + 0x64.        (* mv a0,s0 before the fourth arg_s (0x8c99c) *)
Definition PSB_RET_ARG4 : Z := AF_pins_set + 0x70.     (* auipc a0 of g_rec (0x8c9a8) *)
Definition PSB_REFUSE : Z := AF_pins_set + 0x7c.       (* beqz a0 on g_rec.refuse (0x8c9b4) *)
Definition PSB_MIX_ARM : Z := AF_pins_set + 0x88.      (* ld a0,0x3b0(s1) (0x8c9c0) *)
Definition PSB_RET_MIX : Z := AF_pins_set + 0x94.      (* after mix_call (0x8c9cc) *)
Definition PSB_EPI : Z := AF_pins_set + 0xa0.          (* ld ra,40(sp) (0x8c9d8) *)
Definition PSB_TAIL : Z := AF_pins_set + 0xbc.         (* j answer_code (0x8c9f4) *)

Lemma psb_pcs : cmd_text + AF_pins_set = 0x8c938 /\ cmd_text + PSB_CALL_RECORD = 0x8c968 /\
  cmd_text + PSB_RET_RECORD = 0x8c96c /\ cmd_text + PSB_RET_ARG1 = 0x8c978 /\ cmd_text + PSB_RET_ARG2 = 0x8c984 /\
  cmd_text + PSB_RET_ARG3 = 0x8c990 /\ cmd_text + PSB_DASH = 0x8c994 /\ cmd_text + PSB_JOIN4 = 0x8c99c /\
  cmd_text + PSB_RET_ARG4 = 0x8c9a8 /\ cmd_text + PSB_REFUSE = 0x8c9b4 /\ cmd_text + PSB_MIX_ARM = 0x8c9c0 /\
  cmd_text + PSB_RET_MIX = 0x8c9cc /\ cmd_text + PSB_EPI = 0x8c9d8 /\ cmd_text + PSB_TAIL = 0x8c9f4.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the listing's words at the calls, the tail jump, the two auipc/addi pairs, the two branches and the four
   g_rec accesses (index AF_pins_set / 4 + k for the instruction at 0x8c938 + 4 k) *)
Definition psb_at (k : nat) : option (pinstr csym) := nth_error cmd_listing (Z.to_nat (AF_pins_set / 4) + k).
(* registers as `bv 5`: Reusable's `reg` (a region former) shadows the RISC-V register type here *)
Lemma psb_listing :
  psb_at 12 = Some (PCall CS_record (1%bv : bv 5)) /\ psb_at 15 = Some (PCall CS_arg_s (1%bv : bv 5)) /\
  psb_at 18 = Some (PCall CS_arg_s (1%bv : bv 5)) /\ psb_at 21 = Some (PCall CS_arg_s (1%bv : bv 5)) /\
  psb_at 22 = Some (PW 0x49663) /\
  psb_at 23 = Some (PHi (10%bv : bv 5) 195) /\
  psb_at 24 = Some (PAddHi (9%bv : bv 5) (10%bv : bv 5) 195 (A_OBJ 52) 0x0) /\
  psb_at 27 = Some (PCall CS_arg_s (1%bv : bv 5)) /\
  psb_at 28 = Some (PHi (10%bv : bv 5) 196) /\
  psb_at 29 = Some (PAddHi (9%bv : bv 5) (10%bv : bv 5) 196 (A_OBJ 44) 0x0) /\
  psb_at 30 = Some (PW 0x4a503) /\ psb_at 31 = Some (PW 0x50663) /\ psb_at 32 = Some (PW 0x44a503) /\
  psb_at 34 = Some (PW 0x3b04b503) /\ psb_at 36 = Some (PCall CS_mix_call (1%bv : bv 5)) /\
  psb_at 39 = Some (PW 0x3ab4b823) /\ psb_at 47 = Some (PTail CS_answer_code).
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the A_HI values of the two auipc (0x21994, 0x5e39a8): only addresses, nothing is loaded or stored through them *)
Lemma psb_his : nth 195 cmd_his 0 = 0x21994 /\ nth 196 cmd_his 0 = 0x5e39a8.
Proof. vm_compute. split; reflexivity. Qed.
Lemma psb_objs : nth 52 cmd_objs 0 = 0x21d80 /\ nth 44 cmd_objs 0 = A_G_REC.
Proof. vm_compute. split; reflexivity. Qed.

(* the g_rec fields the code reaches from s1 = g_rec: refuse 0(s1), code 4(s1), state 0x3b0(s1); the answer
   answer_code's pre reads *)
Lemma psb_offs : OFF_REFUSE = 0 /\ OFF_CODE = 4 /\ OFF_STATE = 0x3b0 /\ OFF_ANSWER = 0x390 /\
  A_G_REC + OFF_STATE = 0x5e3670.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the callees' offsets from the listing's base, and the four callees are program functions of the listing *)
Lemma psb_af : cmd_af CS_record = AF_record /\ cmd_af CS_arg_s = AF_arg_s /\
  cmd_af CS_mix_call = AF_mix_call /\ cmd_af CS_answer_code = AF_answer_code /\
  cmd_af CS_pins_set = AF_pins_set.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma psb_prog_syms : In CS_record cmd_prog_syms /\ In CS_arg_s cmd_prog_syms /\
  In CS_mix_call cmd_prog_syms /\ In CS_answer_code cmd_prog_syms.
Proof.
split; [|split; [|split]].
- apply (nth_error_In cmd_prog_syms 23). vm_compute. reflexivity.
- apply (nth_error_In cmd_prog_syms 24). vm_compute. reflexivity.
- apply (nth_error_In cmd_prog_syms 27). vm_compute. reflexivity.
- apply (nth_error_In cmd_prog_syms 49). vm_compute. reflexivity.
Qed.

(* --- the default verdict "-" and the model ----------------------------------------------------------------- *)
Definition psb_dash : list byte := bstr "-".

Lemma psb_dash_lit : RO_lit_21d80 = psb_dash ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma psb_dash_len : Z.of_nat (length psb_dash) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma psb_dash_nonul : ~ In (Z_to_bv 8 0) psb_dash.
Proof.
intros Hz. apply (in_map bv_unsigned) in Hz. vm_compute in Hz.
destruct Hz as [Hz | Hz]; [discriminate Hz | exact Hz].
Qed.

(* the four strings the call records (pins_set_c.v:130 through RecModel.v:89-90) *)
Definition psb_A (uri files layout verdict : option (list byte)) : list (list byte) :=
  [sarg uri; sarg files; sarg layout; darg verdict psb_dash].

Lemma psb_rec_record_scalars : forall X f A,
r_refuse (rec_record X f A) = r_refuse X /\ r_code (rec_record X f A) = r_code X /\
r_state (rec_record X f A) = r_state X /\ r_answer (rec_record X f A) = r_answer X.
Proof. intros X f A. unfold rec_record. destruct (Nat.ltb _ _); destruct X; repeat split. Qed.

(* the refuse arm (0x8c9b4 not taken): answer_code(g_rec.code) on the recorded state *)
Lemma psb_model_refuse : forall R uri files layout verdict, r_refuse R <> 0 ->
pins_set_m R uri files layout verdict =
rec_answer_code (rec_record R REC_PINS_SET (psb_A uri files layout verdict)) (r_code R).
Proof.
intros R uri files layout verdict Hne. unfold pins_set_m, rec_stub_code, psb_A, psb_dash. cbv zeta.
destruct (psb_rec_record_scalars R REC_PINS_SET
  [sarg uri; sarg files; sarg layout; darg verdict (bstr "-"%string)]) as (M1 & M2 & _ & _).
rewrite M1, M2, (proj2 (Z.eqb_neq (r_refuse R) 0) Hne). reflexivity.
Qed.

(* the mix arm (0x8c9b4 taken): mix_call folds the recorded call into g_rec.state, then answer_code(0) *)
Lemma psb_model_mix : forall R uri files layout verdict, r_refuse R = 0 ->
pins_set_m R uri files layout verdict =
rec_answer_code (rec_mix (rec_record R REC_PINS_SET (psb_A uri files layout verdict))
  (REC_PINS_SET, psb_A uri files layout verdict)) 0.
Proof.
intros R uri files layout verdict Hz. unfold pins_set_m, rec_stub_code, psb_A, psb_dash. cbv zeta.
destruct (psb_rec_record_scalars R REC_PINS_SET
  [sarg uri; sarg files; sarg layout; darg verdict (bstr "-"%string)]) as (M1 & _ & _ & _).
rewrite M1, (proj2 (Z.eqb_eq (r_refuse R) 0) Hz). reflexivity.
Qed.

(* the code either arm answers is a 32-bit signed value *)
Lemma psb_model_code : forall R uri files layout verdict, -2 ^ 31 <= r_code R < 2 ^ 31 ->
-2 ^ 31 <= snd (pins_set_m R uri files layout verdict) < 2 ^ 31.
Proof.
intros R uri files layout verdict Hc.
destruct (Z.eq_dec (r_refuse R) 0) as [Hz | Hne].
- rewrite (psb_model_mix R uri files layout verdict Hz). cbn [snd rec_answer_code]. lia.
- rewrite (psb_model_refuse R uri files layout verdict Hne). cbn [snd rec_answer_code]. exact Hc.
Qed.

(* the pointer the fourth arg_s gets (0x8c990-0x8c998): the verdict, or "-" when the verdict is NULL *)
Definition psb_vptr (pv : Z) : Z := if pv =? 0 then 0x21d80 else pv.

Lemma psb_aval_mod : forall rd a n v, aval_mem rd a n v -> aval_mem rd a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof.
intros rd a n v H k Hk. rewrite (H k Hk). unfold le_byte. rewrite Zmod_mod. reflexivity.
Qed.

(* a byte range none of a concrete list of ranges holds *)
Lemma psb_unowned_rng : forall a n (l : list (Z * Z)),
forallb (fun r => (a + n <=? fst r) || (fst r + snd r <=? a)) l = true ->
forall i, 0 <= i < n -> ~ Exists (in_zr (a + i)) l.
Proof.
intros a n l Hb i Hi Hex. apply Exists_exists in Hex as (r & Hr & Hz).
rewrite forallb_forall in Hb. specialize (Hb r Hr). unfold in_zr in Hz.
apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* the conjunct of a long conjunction that holds the literal address [a]: drops the leading conjuncts of H in
   place (no conjunct is unified with the goal, no nested proj2 term is retyped) *)
Local Ltac psb_projz H a :=
  repeat lazymatch type of H with
  | ?A /\ _ => lazymatch A with context [a] => fail | _ => destruct H as [_ H] end
  end;
  lazymatch type of H with
  | _ /\ _ => exact (proj1 H)
  | _ => exact H
  end.

(* membership in a long list of addresses, decided by computation on a closed goal *)
Lemma psb_z_in : forall (a : Z) l, existsb (Z.eqb a) l = true -> In a l.
Proof.
intros a l. induction l as [|x l IH]; cbn [existsb In]; [discriminate|].
intros H. apply orb_true_iff in H as [H|H]; [left; apply Z.eqb_eq in H; symmetry; exact H | right; exact (IH H)].
Qed.

(* the end of "-" is one of the literal ends of CmdRo (a Theorem Labs lane 917ca7ac6b1 regenerated cmd_ro_ends with all 206) *)
Lemma psb_dash_end : In 0x21d81 cmd_ro_ends.
Proof. apply psb_z_in. vm_compute. reflexivity. Qed.

(* the record's checks of "-" (lib/B/Prog/CmdChk.v over lib/B/YF0m's zero-shadow and constant-shadow lists): its
   2 bytes are addressable and its shadow hull is visible *)
Lemma psb_dash_chk : cmd_addr_b 0x21d80 2 = true /\ cmd_hull_b 0x21d80 2 = true.
Proof. split; vm_compute; reflexivity. Qed.

(* --- the recorder's representation --------------------------------------------------------------------------- *)
Lemma psb_acall_in : forall bl rd a c P, acall_at bl rd a c P -> forall pn, In pn P -> In pn bl.
Proof.
intros bl rd a c P (_ & _ & HL & _ & _ & _ & H6) pn Hpn.
destruct (In_nth_error P pn Hpn) as (k & Hk).
assert (Hlt : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hk; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hlt; contradiction].
exact (proj1 (proj2 (proj2 (H6 k s pn Hs Hk)))).
Qed.

Lemma psb_acall_pos : forall bl rd a c P, acall_at bl rd a c P -> forall pn, In pn P -> 0 < snd pn.
Proof.
intros bl rd a c P (_ & _ & HL & _ & _ & _ & H7) pn Hpn.
apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
- destruct (H7 k s pn Hs Hk) as (_ & _ & _ & Hlen & _). lia.
- exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
Qed.

(* every block the representation names is a live block *)
Lemma psb_lay_blocks_in : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q ->
forall pn, In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & HA & HR & _ & _) pn Hpn.
unfold lay_blocks in Hpn.
apply in_app_or in Hpn as [Hc | Hpn]; [|apply in_app_or in Hpn as [Hs | Hpn]; [|apply in_app_or in Hpn as [Ha | Hr]]].
- apply in_concat in Hc as (P & HP & Hin). destruct (In_nth_error _ _ HP) as (i & Hi).
  destruct HC as (_ & HlenQ & _ & Hcalls & _).
  assert (Hlt : (i < length (r_calls R))%nat) by (rewrite <- HlenQ; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc'; [|apply nth_error_Some in Hlt; contradiction].
  exact (psb_acall_in _ _ _ _ _ (proj1 (Hcalls i c P Hc' Hi)) pn Hin).
- destruct HC as (_ & _ & _ & _ & Hsp & _). exact (psb_acall_in _ _ _ _ _ Hsp pn Hs).
- unfold aanswer_at in HA. destruct (r_answer R) as [xa|], (l_answer Q) as [pa|]; cbn [oblk In] in Ha; try contradiction.
  destruct Ha as [<- | []]. exact (proj1 (proj2 (proj2 HA))).
- unfold areply_at in HR. destruct (r_reply R) as [xr|], (l_reply Q) as [pr|]; cbn [oblk In] in Hr; try contradiction.
  destruct Hr as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
Qed.

Lemma psb_lay_ans_in : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
rewrite H. left. reflexivity.
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
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the two auipc/addi pairs leave the objects' addresses in s1 (the statement's VOBJS) *)
Lemma psb_dash_val : cmd_val_objs -> VAL (A_OBJ 52) = 0x21d80.
Proof. intros VOBJS. rewrite (VOBJS 52%nat ltac:(vm_compute; lia)). exact (proj1 psb_objs). Qed.
Lemma psb_grec_val : cmd_val_objs -> VAL (A_OBJ 44) = A_G_REC.
Proof. intros VOBJS. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). exact (proj2 psb_objs). Qed.

(* the call targets: each callee's entry is BASE + AF_<fn>, from the walk fact cmd_sig_prog (record's is the kit's
   CmdRecAns.v rca_sig_record) *)
Section s.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Lemma psb_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (cmd_sig_prog_PB CS_arg_s (proj1 (proj2 psb_prog_syms))), (proj1 (proj2 psb_af)). reflexivity. Qed.
Lemma psb_sig_mix_call : SIG CS_mix_call = BASE + AF_mix_call.
Proof.
rewrite (cmd_sig_prog_PB CS_mix_call (proj1 (proj2 (proj2 psb_prog_syms)))), (proj1 (proj2 (proj2 psb_af))).
reflexivity.
Qed.
Lemma psb_sig_answer_code : SIG CS_answer_code = BASE + AF_answer_code.
Proof.
rewrite (cmd_sig_prog_PB CS_answer_code (proj2 (proj2 (proj2 psb_prog_syms)))), (proj1 (proj2 (proj2 (proj2 psb_af)))).
reflexivity.
Qed.
End s.

Section e.
Variable B : asyms.
(* the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), under its canonical name (RECB-NAMED-HYPS.md) *)
Hypothesis HB : CmdBSyms B.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
(* --- the string arguments ------------------------------------------------------------------------------------ *)
(* "-" as a recorder argument (astr_argA's read-only arm, lib/B/Prog/CmdRep.v): its bytes from cmd_ro_ok (CmdRo's
   0x21d80 conjunct), its read-only range from the walk fact cmd_ro_in (the A walk's CMD_RO_IN), the record's checks
   cmd_addr_b / cmd_hull_b and its end in cmd_ro_ends by computation, unowned and not errno from HB *)
Lemma psb_dash_arg : forall ly S (W : world SEGS) mem O,
cmd_ro_ok (rdW W mem) -> cmd_ro_in (in_roP SEGS RLO RHI) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O 0x21d80 (Some psb_dash).
Proof.
intros ly S W mem O HROK HRI.
assert (HLIT : abytes_atR (rdW W mem) 0x21d80 RO_lit_21d80).
{ destruct HROK as [HBY _]. unfold cmd_ro_bytes in HBY. psb_projz HBY 0x21d80. }
assert (HLITro : forall i, 0 <= i < 2 -> in_roP SEGS RLO RHI (0x21d80 + i)).
{ unfold cmd_ro_in in HRI. psb_projz HRI 0x21d80. }
rewrite psb_dash_lit in HLIT. cbn [astr_argA]. rewrite psb_dash_len.
split; [lia|]. split; [split; [exact HLIT | exact psb_dash_nonul]|].
split; [unfold LMAX; lia|]. right. split; [|split; [|split]].
- intros i Hi. split; [apply HLITro; lia|]. rewrite (ts_owned B HB), (ts_errno B HB). split.
  + apply (psb_unowned_rng 0x21d80 2); [vm_compute; reflexivity | lia].
  + unfold TFIB_ERRNO. lia.
- exact (proj1 psb_dash_chk).
- exact (proj2 psb_dash_chk).
- change (Z.of_nat (length psb_dash)) with 1. exact psb_dash_end.
Qed.

(* the word after the terminator of "-", which arg_s's strlen wrapper reads, is readable: cmd_ro_ok's cmd_ro_tails at
   the literal end 0x21d81 *)
Lemma psb_dash_tail : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) ->
atail_vis SEGS W mem (0x21d80 + Z.of_nat (length psb_dash)).
Proof.
intros W mem [_ HT] a Ha. change (0x21d80 + Z.of_nat (length psb_dash)) with 0x21d81 in Ha.
exact (HT 0x21d81 psb_dash_end a Ha).
Qed.

(* the branch at 0x8c990: the verdict pointer is 0 exactly when the verdict is NULL *)
Lemma psb_verdict_null : forall ly S rd ro O pv verdict,
astr_argA B ly S rd ro O pv verdict -> (pv = 0 <-> verdict = None).
Proof.
intros ly S rd ro O pv [x|] Hv; cbn [astr_argA] in Hv; split; intros H.
- exfalso. exact (proj1 Hv H).
- discriminate H.
- reflexivity.
- exact Hv.
Qed.

(* the fourth arg_s's argument (0x8c99c-0x8c9a4): s1 = psb_vptr pv, the string darg verdict "-" *)
Lemma psb_verdict_arg : forall ly S (W : world SEGS) mem O pv verdict,
cmd_ro_ok (rdW W mem) -> cmd_ro_in (in_roP SEGS RLO RHI) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verdict ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O (psb_vptr pv) (Some (darg verdict psb_dash)).
Proof.
intros ly S W mem O pv [x|] HROK HRI Hv; cbn [darg].
- unfold psb_vptr. destruct (Z.eqb_spec pv 0) as [E|E]; [|exact Hv].
  exfalso. cbn [astr_argA] in Hv. exact (proj1 Hv E).
- cbn [astr_argA] in Hv. subst pv. exact (psb_dash_arg ly S W mem O HROK HRI).
Qed.

(* a string the statement gives as a heap block (pins_set_c.v:106-114) is astr_argA's block arm *)
Lemma psb_blk_arg : forall ly S (W : world SEGS) mem md O p x,
AR SEGS B ly S W mem md ->
in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) p x -> Z.of_nat (length x) + 1 <= LMAX + 1 ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros ly S W mem md O p x HAR Hblk HapO Hstr Hn.
destruct Hblk as (q & m & Hqm & Hq1 & Hq2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & H4096 & _).
split; [lia|]. split; [exact Hstr|]. split; [exact Hn|].
left. split; [exists q, m; split; [exact Hqm | lia] | exact HapO].
Qed.

(* --- the recorder ------------------------------------------------------------------------------------------- *)
(* the recorder's own blocks are live blocks of positive size *)
Lemma psb_O_facts : forall ly S rd R O, rec_repA B ly S rd R O ->
forall pn, In pn O -> 0 < snd pn /\ In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn.
split; [|exact (psb_lay_blocks_in _ _ _ _ _ _ HA pn Hpn)].
destruct HA as (_ & _ & _ & (_ & HlenQ & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
unfold lay_blocks in Hpn. apply in_app_or in Hpn as [Hpn | Hpn];
  [|apply in_app_or in Hpn as [Hpn | Hpn]; [|apply in_app_or in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
  + exact (psb_acall_pos _ _ _ _ _ (proj1 (Hc4 i c P Hc Hi)) pn Hin).
  + exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- exact (psb_acall_pos _ _ _ _ _ Hsp pn Hpn).
- unfold aanswer_at in Ha. destruct (r_answer R) as [x|], (l_answer Q) as [q|]; cbn [oblk] in Hpn; try contradiction.
  destruct Hpn as [<- | []]. destruct Ha as (_ & _ & _ & Hl & _). lia.
- unfold areply_at in Hr. destruct (r_reply R) as [x|], (l_reply Q) as [q|]; cbn [oblk] in Hpn; try contradiction.
  destruct Hpn as [<- | []]. destruct Hr as (_ & _ & _ & Hne & _ & Hl & _).
  destruct x as [|b x]; [exfalso; exact (Hne eq_refl)|]. cbn [length] in Hl. lia.
Qed.

(* two live blocks with the same start are the same block *)
Lemma psb_same_start : forall ly S (W : world SEGS) mem md p n m,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (p, m) (ablocks B ly S) -> n = m.
Proof.
intros ly S W mem md p n m HAR H1 H2.
destruct (Z.eq_dec n m) as [->|Hne]; [reflexivity|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p n p m HAR H1 H2
  ltac:(intros E; injection E as E'; exact (Hne E'))) as D.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR H1) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR H2) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos n ltac:(lia)) as [Qn _]. pose proof (req_size_pos m ltac:(lia)) as [Qm _].
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* the scalars the B code reads through s1 = g_rec: refuse (lw 0(s1), 0x8c9b0), code (lw 4(s1), 0x8c9b8), state
   (ld 0x3b0(s1), 0x8c9c0) *)
Lemma psb_scalars : forall ly S rd R O, rec_repA B ly S rd R O ->
aval_mem rd (A_G_REC + OFF_REFUSE) 4 (r_refuse R) /\ aval_mem rd (A_G_REC + OFF_CODE) 4 (r_code R) /\
aval_mem rd (A_G_REC + OFF_STATE) 8 (r_state R) /\
-2 ^ 31 <= r_refuse R < 2 ^ 31 /\ -2 ^ 31 <= r_code R < 2 ^ 31 /\ 0 <= r_state R < 2 ^ 64.
Proof.
intros ly S rd R O (Q & HA & _). destruct HA as (_ & _ & _ & _ & _ & _ & HS & _).
destruct HS as (H1 & H2 & _ & H4 & _ & B1 & B2 & _ & B4 & _).
repeat split; assumption || lia.
Qed.

(* the answer the recorder holds (answer_code's `old`, tanswer_code_spec's aval_mem premise): 0, or the start of
   one of its blocks, a 64-bit word; a live block that starts there is the recorder's *)
Lemma psb_old_answer : forall ly S (W : world SEGS) mem md R O,
AR SEGS B ly S W mem md -> rec_repA B ly S (rdW W mem) R O ->
exists old, aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old /\ 0 <= old < 2 ^ 64 /\
(old = 0 \/ exists pa, In pa O /\ fst pa = old) /\
(forall pn, In pn (ablocks B ly S) -> fst pn = old -> In pn O).
Proof.
intros ly S W mem md R O HAR HREP.
pose proof asan_consts as (C1 & _).
assert (HOL : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (proj2 (psb_O_facts ly S _ R O HREP pn Hpn))).
assert (HOLD : exists old, aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old /\
  (old = 0 \/ exists pa, In pa O /\ fst pa = old)).
{ pose proof HREP as (Q & HA & HO).
  destruct HA as (_ & _ & _ & _ & HAns & _). unfold aanswer_at in HAns.
  destruct (r_answer R) as [x|], (l_answer Q) as [pa|] eqn:Eq; try contradiction.
  - exists (fst pa). split; [exact (proj1 HAns)|]. right. exists pa.
    split; [apply HO; exact (psb_lay_ans_in Q pa Eq) | reflexivity].
  - exists 0. split; [exact HAns | left; reflexivity]. }
destruct HOLD as (old & HOLDV & HOLDC).
exists old. split; [exact HOLDV|]. split; [|split; [exact HOLDC|]].
- destruct HOLDC as [-> | ([p n] & Hpa & Hpf)]; [lia|]. cbn [fst] in Hpf. subst p.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ old n HAR (HOL _ Hpa)) as (_ & H4096 & Hce & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [Qn _]. clear HOLDV HAR HREP HOL Hpa. lia.
- intros [p n] Hpn Hf. cbn [fst] in Hf.
  destruct HOLDC as [E0 | ([pp pm] & Hpa & Hpf)].
  + exfalso. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & H4096 & _). lia.
  + cbn [fst] in Hpf. subst pp. subst p.
    pose proof (psb_same_start ly S W mem md old n pm HAR Hpn (HOL _ Hpa)) as En.
    subst pm. exact Hpa.
Qed.

End e.
End f.
End d.
