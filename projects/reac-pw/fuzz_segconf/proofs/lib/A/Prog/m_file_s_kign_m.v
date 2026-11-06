(* m_file on fuzz_segconf.asan (image A): the inner cuts of segment S_MF_KIGNP (KIGN 0x8693c -> KKNOCK 0x86b20 or
   KDONE 0x86cd0; the G2 walk owner's guide/MF-CUTS-A.md section 4, S_MF_KIGNP), in the form of lib/A/Prog/m_file_m.v's
   cut statements, and the chain that gives S_MF_KIGNP from the inner pieces. Statement text and logic only (no
   instruction is executed here). The KIGNP segment lane of the G2 walk owner's G2.
   proves no function (kind: segment lemma of m_file's walk: the inner statements of S_MF_KIGNP).

   What the piece does (listing m_file.fuzz_segconf.asan.s, 0x8693c-0x86a40, 0x86c84-0x86cbc): ieq(k, kl,
   "ignore") 0x8694c; 0 goes to KKNOCK (`beqz` 0x86950). Else the value v = [ov, ov + vl) is tested in this order:
   ieq(v, vl, "yes") 0x86964 (s6 = 1 at 0x86968), ieq "true" 0x86980, vl = 1 and v[0] = '1' (an inline load1 check of
   v, 0x8699c, then `lbu` 0x869a4), ieq "no" 0x869c0, ieq "false" 0x869d8 (s6 = 0 at 0x869e0 for these two), then at
   0x86c84 s6 = line + 1 and s8 = FAKE, vl = 1 and v[0] = '0' (load1 check 0x86ca0, `lbu` 0x86ca8; then s8 = line + 1,
   s6 = 0 and `j 0x869e8`). A hit reaches 0x869e8 with a3 = cur = g: g->ignore = s6 (store4 check 0x869f4, `sw`
   0x869fc), s5 = c, g->ignore_set = 1 (store4 check 0x86a0c, `sw` 0x86a1c), snprintf(g + 156, 96, "%s", c->reading)
   0x86a34, s6 = line + 1, s8 = FAKE, `j` KDONE. A bad value goes from 0x86c94 / 0x86cb0 to 0x86cc0, S_MF_KMOD's
   m_refuse block (MK_REFUSE_stmt, lib/A/Prog/m_file_s_kmod_m.v).

   THE INNER CUTS (A pc; listing offset = AF_m_file + (pc - 0x85ebc)), each a return point of an ieq call or the
   hit path's start:
     KI_R1  0x86950 (+0xa94)  ieq(k, kl, "ignore") returned
     KI_R2  0x86968 (+0xaac)  ieq(v, vl, "yes") returned
     KI_R3  0x86984 (+0xac8)  ieq(v, vl, "true") returned (s6 = 1)
     KI_R4  0x869c4 (+0xb08)  ieq(v, vl, "no") returned
     KI_R5  0x869dc (+0xb20)  ieq(v, vl, "false") returned
     KI_HIT 0x869e8 (+0xb2c)  the value accepted: a3 = g, s6 = the flag, s8 = line + 1
   At each the K cut's state (m_file_m.v MF_KAT_stmt) holds; from KI_R2 on only the value's registers are kept
   (s5 = v, s4 = vl) besides s8 = line + 1, and the model equation is the K cut's with mk_disp reduced by
   "ignore" hit to ki_val (the value test ki_dec of m_file_s_kign_t.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_kign_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================================== the inner cut points ===================================== *)
Definition KI_R1 : Z := AF_m_file + 0xa94.    (* 0x86950, ieq "ignore" returned *)
Definition KI_R2 : Z := AF_m_file + 0xaac.    (* 0x86968, ieq "yes" returned *)
Definition KI_R3 : Z := AF_m_file + 0xac8.    (* 0x86984, ieq "true" returned *)
Definition KI_R4 : Z := AF_m_file + 0xb08.    (* 0x869c4, ieq "no" returned *)
Definition KI_R5 : Z := AF_m_file + 0xb20.    (* 0x869dc, ieq "false" returned *)
Definition KI_HIT : Z := AF_m_file + 0xb2c.   (* 0x869e8, the value accepted *)

(* the K cut's model step once "ignore" hit (SegModel.m_key's S_ignore arm, in the code's order) *)
Definition ki_val (c : mconf) (gi : nat) (vv : list Z) (line : Z) : mconf :=
  match ki_dec vv with
  | Some b => m_upd c gi (ms_with_ignore b (snprintf_s 96 F_s [AS (mc_reading c)]))
  | None => m_refuse c line false
  end.

Lemma ki_val_disp : forall c gi k vv line,
  ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = true ->
  mk_disp c gi k vv line = ki_val c gi vv line.
Proof.
intros c gi k vv line H1 H2 H3. unfold ki_val. destruct (ki_dec vv) as [b|] eqn:E.
- exact (ki_disp_hit c gi k vv line b H1 H2 H3 E).
- exact (ki_disp_ref c gi k vv line H1 H2 H3 E).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the K cut's state with the key (MF_KAT_stmt's premises but the words missed and the model equation) *)
Definition ki_kbase (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
(memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
(ok kl ov vl : nat) (k vv : list Z) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc /\ mf_cells v lyc pos memc Wc (Some gi) /\
mf_regs_at B v lyc pos regs1 /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc (Some gi) line p rest /\
mk_kv rest ok kl ov vl k vv /\
getr regs1 27 = w64 (p + Z.of_nat ok) /\ getr regs1 22 = w64 (Z.of_nat kl) /\
getr regs1 21 = w64 (p + Z.of_nat ov) /\ getr regs1 20 = w64 (Z.of_nat vl) /\
getr regs1 23 = w64 (p + Z.of_nat (ov + vl)) /\ getr regs1 24 = w64 (line + 1) /\
mf_np v memc Wc (mf_next p rest).

(* the value's state (from KI_R2 on): the key is no longer read; s5 = v, s4 = vl, s8 = line + 1 *)
Definition ki_vbase (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
(memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
(ov vl : nat) (vv : list Z) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc /\ mf_cells v lyc pos memc Wc (Some gi) /\
mf_regs_at B v lyc pos regs1 /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc (Some gi) line p rest /\
(ov + vl <= length (mf_line rest))%nat /\ firstn vl (skipn ov rest) = vv /\
mf_np v memc Wc (mf_next p rest) /\
getr regs1 21 = w64 (p + Z.of_nat ov) /\ getr regs1 20 = w64 (Z.of_nat vl) /\ getr regs1 24 = w64 (line + 1).

(* 0x86950: ieq(k, kl, "ignore") returned in a0 *)
Definition KI_R1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
ki_kbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv ->
Forall (fun w => ieq k w = false) [S_role; S_model] ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
getr regs1 10 = w64 (seg_spec.b2z (ieq k S_ignore)) ->
mf_at B v Wc regs1 memc mdc KI_R1.

(* 0x86968: ieq(v, vl, "yes") returned in a0 *)
Definition KI_R2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
getr regs1 10 = w64 (seg_spec.b2z (ieq vv S_yes)) ->
mf_at B v Wc regs1 memc mdc KI_R2.

(* 0x86984: ieq(v, vl, "true") returned in a0; "yes" missed; s6 = 1 *)
Definition KI_R3_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
ieq vv S_yes = false ->
getr regs1 10 = w64 (seg_spec.b2z (ieq vv S_true)) -> getr regs1 22 = w64 1 ->
mf_at B v Wc regs1 memc mdc KI_R3.

(* 0x869c4: ieq(v, vl, "no") returned in a0; "yes", "true" and "1" missed *)
Definition KI_R4_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
ieq vv S_yes = false -> ieq vv S_true = false -> ~ (length vv = 1%nat /\ hd0 vv = 49) ->
getr regs1 10 = w64 (seg_spec.b2z (ieq vv S_no)) ->
mf_at B v Wc regs1 memc mdc KI_R4.

(* 0x869dc: ieq(v, vl, "false") returned in a0; "yes", "true", "1" and "no" missed *)
Definition KI_R5_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
ieq vv S_yes = false -> ieq vv S_true = false -> ~ (length vv = 1%nat /\ hd0 vv = 49) -> ieq vv S_no = false ->
getr regs1 10 = w64 (seg_spec.b2z (ieq vv S_false)) ->
mf_at B v Wc regs1 memc mdc KI_R5.

(* 0x869e8: the value accepted as b; a3 = g = &c->seg[gi], s6 = b *)
Definition KI_HIT_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z) (b : bool),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (m_upd mcc gi (ms_with_ignore b (snprintf_s 96 F_s [AS (mc_reading mcc)])), Some gi) line rest = mf_final v ->
getr regs1 13 = w64 (seg_spec.mseg_addr (mv_c v) gi) -> getr regs1 22 = w64 (seg_spec.b2z b) ->
mf_at B v Wc regs1 memc mdc KI_HIT.

End e.
End f.
End d.
