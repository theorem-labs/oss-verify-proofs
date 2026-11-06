(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): the inner cuts of
   segment S_MF_KIGNP (KIGN 0x86968 -> KKNOCK 0x86a7c or KDONE 0x86c1c; the image-B m_file segment table section 9,
   the image-B m_file cut map section 4 S_MF_KIGNP), in the form of lib/B/Prog/m_file_m.v's cut statements. Statement text
   and logic only (no instruction is executed here). A walk lane of the image-B m_file-family owner's G2B. ADAPTED from the image-A m_file-family lane's
   image-A lib/A/Prog/m_file_s_kign_m.v (commit a11e040adbd4) at image B's pcs, registers and
   frame cells.
   proves no function (kind: segment lemma of m_file's walk: the inner statements of S_MF_KIGNP).

   What the piece does (the neutral listing of m_file in image B; owned 0x86968-0x86a78, 0x86bdc-0x86c04,
   0x86cd0-0x86cec, 0x86d88-0x86d9c, 0x86f18-0x86f1c, 0x86f54; also runs 0x86c08-0x86c18 and the trap 0x86e84):
   KIGN 0x86968: a0 = k (208(s1)), a1 = kl (s5), a2 = "ignore" (listing object 20, 0x21240), ieq 0x86978; at
   0x8697c s9 = 112(s1) (= c); 0 goes to KKNOCK (`beqz` 0x86980). Else the value v = [ov, ov + vl) (192(s1), s10 =
   vl) is tested in this order: ieq(v, vl, "yes") 0x86994 (s4 = 1 at 0x86998, a hit `bnez` 0x8699c), ieq "true"
   0x869b0 (`bnez` 0x869b4), vl = 1 (0x869bc) and v[0] = '1' (the trap 0x869c4 on v = NULL, the load1 check
   0x869d0 of v, slow path 0x86d88, error path 0x86f54; `lbu` 0x869d8, `beq` 0x869e0), ieq "no" 0x869f4 (`bnez`
   0x869f8 to 0x86a14), ieq "false" 0x86a0c (0 to 0x86bdc), s4 = 0 at 0x86a14; at 0x86bdc vl = 1 (0x86be0) and
   v[0] = '0' (trap 0x86be8, load1 check 0x86bf4, slow path 0x86d94, error path 0x86d9c; `lbu` 0x86bfc, `beq`
   0x86c04 to 0x86a14), else the refusal 0x86c08 (S_MF_KMOD's block: s9 = 112(s1), m_refuse(c, line + 1)
   0x86c14, s4 = 511 0x86c18, KDONE). A hit reaches 0x86a18 with s4 = b: the trap 0x86a20 (cur & 3, cur =
   136(s1)), a3 = cur; g->ignore = s4 (store4 check 0x86a34, slow path 0x86cd0, error path 0x86f18; `sw`
   0x86a3c), s9 = 112(s1) (0x86a50), g->ignore_set = 1 (store4 check 0x86a4c, slow path 0x86ce0, error path
   0x86f1c; `sw` 0x86a5c), snprintf(g + 156, 96, "%s", c->reading = 64(s1)) 0x86a74, `j` 0x86c18 (s4 = 511),
   KDONE.

   THE INNER CUTS (B pc; listing offset = AF_m_file + (pc - 0x86140)), each a return point of an ieq call, the
   hit path's start or the refusal's start:
     KI_R1  0x8697c (+0x83c)  ieq(k, kl, "ignore") returned
     KI_R2  0x86998 (+0x858)  ieq(v, vl, "yes") returned
     KI_R3  0x869b4 (+0x874)  ieq(v, vl, "true") returned (s4 = 1)
     KI_R4  0x869f8 (+0x8b8)  ieq(v, vl, "no") returned
     KI_R5  0x86a10 (+0x8d0)  ieq(v, vl, "false") returned
     KI_HIT 0x86a18 (+0x8d8)  the value accepted: s4 = the flag
     KI_REF 0x86c08 (+0xac8)  the value refused: the refusal block
   At each the K cut's state (m_file_m.v MF_KAT_stmt) holds; from KI_R2 on only the value's cells are kept
   (192(s1) = v, s10 = vl) besides s11 = line + 1 and 152(s1) = the next line's address, and the model equation is
   the K cut's with mk_disp reduced by "ignore" hit to ki_val (the value test ki_dec of mf_kignp_t.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m mf_kignp_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================================== the inner cut points ===================================== *)
Definition KI_R1 : Z := AF_m_file + 0x83c.    (* 0x8697c, ieq "ignore" returned *)
Definition KI_R2 : Z := AF_m_file + 0x858.    (* 0x86998, ieq "yes" returned *)
Definition KI_R3 : Z := AF_m_file + 0x874.    (* 0x869b4, ieq "true" returned *)
Definition KI_R4 : Z := AF_m_file + 0x8b8.    (* 0x869f8, ieq "no" returned *)
Definition KI_R5 : Z := AF_m_file + 0x8d0.    (* 0x86a10, ieq "false" returned *)
Definition KI_HIT : Z := AF_m_file + 0x8d8.   (* 0x86a18, the value accepted *)
Definition KI_REF : Z := AF_m_file + 0xac8.   (* 0x86c08, the value refused (S_MF_KMOD's refusal block) *)
(* the two returns that go on to m_key's common end: snprintf's 0x86a78 (`j 0x86c18`) and m_refuse's 0x86c18
   (`li s4,511`), both followed by KDONE 0x86c1c *)
Definition KI_SNR : Z := AF_m_file + 0x938.   (* 0x86a78, after snprintf(g->ignore_file, ..) *)
Definition KI_S4 : Z := AF_m_file + 0xad8.    (* 0x86c18, after m_refuse; li s4,511 *)

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

(* the K cut's state with the key (MF_KAT_stmt's premises but the words missed and the model equation, with a0
   free): 208(s1) = k, s5 = kl, 192(s1) = v, s10 = vl, s11 = line + 1, 152(s1) = the next line's address *)
Definition ki_kbase (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
(memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
(ok kl ov vl : nat) (k vv : list Z) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc /\ mf_cells v lyc pos memc Wc (Some gi) /\
mf_regs_at B v lyc pos regs1 /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc (Some gi) line p rest /\
mk_kv rest ok kl ov vl k vv /\
mf_slot v memc Wc 208 (p + Z.of_nat ok) /\ getr regs1 21 = w64 (Z.of_nat kl) /\
mf_slot v memc Wc 192 (p + Z.of_nat ov) /\ getr regs1 26 = w64 (Z.of_nat vl) /\
getr regs1 27 = w64 (line + 1) /\ mf_np v memc Wc (mf_next p rest).

(* the value's state (from KI_R2 on): the key is no longer read; 192(s1) = v, s10 = vl, s11 = line + 1 *)
Definition ki_vbase (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
(memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
(ov vl : nat) (vv : list Z) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc /\ mf_cells v lyc pos memc Wc (Some gi) /\
mf_regs_at B v lyc pos regs1 /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc (Some gi) line p rest /\
(ov + vl <= length (mf_line rest))%nat /\ firstn vl (skipn ov rest) = vv /\
mf_slot v memc Wc 192 (p + Z.of_nat ov) /\ getr regs1 26 = w64 (Z.of_nat vl) /\
getr regs1 27 = w64 (line + 1) /\ mf_np v memc Wc (mf_next p rest).

(* 0x8697c: ieq(k, kl, "ignore") returned in a0 *)
Definition KI_R1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
ki_kbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv ->
Forall (fun w => ieq k w = false) [S_role; S_model] ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
getr regs1 10 = w64 (seg_spec.b2z (ieq k S_ignore)) ->
mf_at B v Wc regs1 memc mdc KI_R1.

(* 0x86998: ieq(v, vl, "yes") returned in a0 *)
Definition KI_R2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
getr regs1 10 = w64 (seg_spec.b2z (ieq vv S_yes)) ->
mf_at B v Wc regs1 memc mdc KI_R2.

(* 0x869b4: ieq(v, vl, "true") returned in a0; "yes" missed; s4 = 1 *)
Definition KI_R3_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
ieq vv S_yes = false ->
getr regs1 10 = w64 (seg_spec.b2z (ieq vv S_true)) -> getr regs1 20 = w64 1 ->
mf_at B v Wc regs1 memc mdc KI_R3.

(* 0x869f8: ieq(v, vl, "no") returned in a0; "yes", "true" and "1" missed *)
Definition KI_R4_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
ieq vv S_yes = false -> ieq vv S_true = false -> ~ (length vv = 1%nat /\ hd0 vv = 49) ->
getr regs1 10 = w64 (seg_spec.b2z (ieq vv S_no)) ->
mf_at B v Wc regs1 memc mdc KI_R4.

(* 0x86a10: ieq(v, vl, "false") returned in a0; "yes", "true", "1" and "no" missed *)
Definition KI_R5_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
ieq vv S_yes = false -> ieq vv S_true = false -> ~ (length vv = 1%nat /\ hd0 vv = 49) -> ieq vv S_no = false ->
getr regs1 10 = w64 (seg_spec.b2z (ieq vv S_false)) ->
mf_at B v Wc regs1 memc mdc KI_R5.

(* 0x86a18: the value accepted as b; s4 = b (cur = &c->seg[gi] is in 136(s1), mf_cells) *)
Definition KI_HIT_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z) (b : bool),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (m_upd mcc gi (ms_with_ignore b (snprintf_s 96 F_s [AS (mc_reading mcc)])), Some gi) line rest = mf_final v ->
getr regs1 20 = w64 (seg_spec.b2z b) ->
mf_at B v Wc regs1 memc mdc KI_HIT.

(* 0x86c08: the value refused: m_refuse(c, line + 1) at 0x86c14, cur kept *)
Definition KI_REF_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
ki_vbase n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (m_refuse mcc (line + 1) false, Some gi) line rest = mf_final v ->
mf_at B v Wc regs1 memc mdc KI_REF.

(* KI_SNR 0x86a78 / KI_S4 0x86c18: the line's model step done (the block holds mcc', the line's model mcl moved by
   one refusal at most, cur = Some gi kept), the K state's frame without the key and the value; s4 free *)
Definition KI_DONE_stmt (pc : Z) (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc' mcl : mconf) (gi : nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc' -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcl (Some gi) line p rest ->
mc_refused mcc' <= mc_refused mcl + 1 -> mc_overflow mcc' <= mc_overflow mcl + 1 ->
(length (mc_kept mcl) <= length (mc_kept mcc'))%nat -> (gi < length (mc_seg mcc'))%nat ->
mf_fin (mcc', Some gi) line rest = mf_final v ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc pc.

End e.
End f.
End d.
