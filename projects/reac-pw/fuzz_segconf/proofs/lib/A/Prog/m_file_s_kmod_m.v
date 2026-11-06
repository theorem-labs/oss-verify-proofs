(* m_file on fuzz_segconf.asan (image A): the inner cuts of segment S_MF_KMOD (KMODEL 0x867b8 -> KIGN 0x8693c or
   KDONE 0x86cd0; the G2 walk owner's guide/MF-CUTS-A.md section 4, S_MF_KMOD), in the form of lib/A/Prog/m_file_m.v's
   cut statements. Statement text only. The KMOD segment lane of the G2 walk owner's G2.

   What the piece does (listing m_file.fuzz_segconf.asan.s): ieq(k, kl, "model") 0x867c8; 0 goes to KIGN; else
   ln = min(vl, 23) in s4 (0x867d0-0x867d8), s6 = line + 1 and s8 = FAKE (0x867dc, 0x867e0), an empty value skips
   the fold (`beq s7,s5` 0x867e4); the fold 0x867f8-0x86844 writes low[i] = lower(v[i]) for i < ln (a0 = s5 the
   value cursor, a1 = a2 the low cursor, a3 = ln - i counting down; inline checks load1 0x86800 and store1 0x86810);
   0x86864: s5 = low, low[ln] = 0 (no check), fuzz_catalogue_row(low, ln) 0x86878; NULL goes to 0x86cc0: m_refuse(c,
   line + 1) 0x86ccc, then KDONE; else 0x86880: s7 = cur = g, __asan_memcpy(g + 36, low, ln + 1) 0x86890, the check
   of g->model_set (store4 0x868a0), g->model_set = 1 (0x868b0), s5 = c, then KDONE.

   THE INNER CUTS (A pc; listing offset = AF_m_file + (pc - 0x85ebc)):
     MK_FOLD   0x867f8 (+0x93c)  the fold's head, value byte i (0 <= i < ln)
     MK_FEXIT  0x86864 (+0x9a8)  the fold done: low[0 .. ln) = h_fold v 24
     MK_CPY    0x86880 (+0x9c4)  fuzz_catalogue_row found the row: low[0 .. ln] = h_fold v 24 ++ [0]
     MK_REFUSE 0x86cc0 (+0xe04)  m_refuse of the line (the row is NULL; also KIGNP's bad value)
   At each the K-cut state of m_file_m.v's MF_KAT_stmt holds with the key no longer needed: cur = Some gi, the value
   vv = the bytes [ov, ov + vl) of the text left, inside the line, low.i in scope (MF_LOW_ON), the next line's
   address in 144(s1); s6 = line + 1 and s8 = FAKE (moved back at 0x867dc / 0x867e0); the model equation is the K
   cut's with ieq k "role" = false and ieq k "model" = true (mk_disp_model below), the branch on the row taken at
   MK_CPY and MK_REFUSE. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================================== the inner cut points ===================================== *)
Definition MK_FOLD : Z := AF_m_file + 0x93c.     (* 0x867f8, the fold's head *)
Definition MK_FEXIT : Z := AF_m_file + 0x9a8.    (* 0x86864, after the fold *)
Definition MK_CPY : Z := AF_m_file + 0x9c4.      (* 0x86880, the row was found *)
Definition MK_REFUSE : Z := AF_m_file + 0xe04.   (* 0x86cc0, m_refuse of the line *)

(* ln = min(vl, 23), s4 from 0x867d8 on: the fold's count (fold(v, vl, low, 24), H:141-148) *)
Definition mk_ln (vl : nat) : nat := Nat.min vl 23.
(* the model branch of mk_disp (SegModel.m_key's `ieq k S_model` arm) *)
Definition mk_mod (c : mconf) (gi : nat) (vv : list Z) (line : Z) : mconf :=
  match cat_row (h_fold vv 24) with
  | None => m_refuse c line false
  | Some _ => m_upd c gi (ms_with_model (h_fold vv 24))
  end.

Lemma mk_disp_model : forall c gi k vv line,
  ieq k S_role = false -> ieq k S_model = true -> mk_disp c gi k vv line = mk_mod c gi vv line.
Proof. intros c gi k vv line H1 H2. unfold mk_disp, mk_mod. rewrite H1, H2. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the state every inner cut has: the K cut's (MF_KAT_stmt) without the key, with s8 = FAKE and s6 = line + 1 *)
Definition mk_base (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
(memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
(ov vl : nat) (vv : list Z) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc /\ mf_cells v lyc pos memc Wc (Some gi) /\
mf_regs_at B v lyc pos regs1 /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc (Some gi) line p rest /\
(ov + vl <= length (mf_line rest))%nat /\ firstn vl (skipn ov rest) = vv /\
mf_np v memc Wc (mf_next p rest) /\
getr regs1 24 = w64 (frame_addr lyc 1 pos) /\ getr regs1 22 = w64 (line + 1).

(* 0x867f8, the fold's head at value byte i: low[0 .. i) folded; a0 = s5 = v + i, a1 = a2 = low + i, a3 = ln - i,
   s4 = ln *)
Definition MK_FOLD_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z) (i : nat),
mk_base n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (mk_mod mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
(i < mk_ln vl)%nat ->
sa_zs (rdW Wc memc) (frame_addr lyc 1 pos + 32) (map lower (firstn i vv)) ->
getr regs1 20 = w64 (Z.of_nat (mk_ln vl)) ->
getr regs1 21 = w64 (p + Z.of_nat (ov + i)) -> getr regs1 10 = w64 (p + Z.of_nat (ov + i)) ->
getr regs1 11 = w64 (frame_addr lyc 1 pos + 32 + Z.of_nat i) ->
getr regs1 12 = w64 (frame_addr lyc 1 pos + 32 + Z.of_nat i) ->
getr regs1 13 = w64 (Z.of_nat (mk_ln vl - i)) ->
mf_at B v Wc regs1 memc mdc MK_FOLD.

(* 0x86864, the fold done: low[0 .. ln) = h_fold vv 24, s4 = ln *)
Definition MK_FEXIT_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
mk_base n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (mk_mod mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
sa_zs (rdW Wc memc) (frame_addr lyc 1 pos + 32) (h_fold vv 24) ->
getr regs1 20 = w64 (Z.of_nat (mk_ln vl)) ->
mf_at B v Wc regs1 memc mdc MK_FEXIT.

(* 0x86880, the row found: low[0 .. ln] = h_fold vv 24 ++ [0], s5 = low, s4 = ln *)
Definition MK_CPY_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z) (r : nat),
mk_base n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
cat_row (h_fold vv 24) = Some r ->
mf_fin (m_upd mcc gi (ms_with_model (h_fold vv 24)), Some gi) line rest = mf_final v ->
sa_zs (rdW Wc memc) (frame_addr lyc 1 pos + 32) (h_fold vv 24 ++ [0]) ->
getr regs1 20 = w64 (Z.of_nat (mk_ln vl)) -> getr regs1 21 = w64 (frame_addr lyc 1 pos + 32) ->
mf_at B v Wc regs1 memc mdc MK_CPY.

(* 0x86cc0, m_refuse of the line (c from 128(s1), the line number in s6) *)
Definition MK_REFUSE_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ov vl : nat)
  (vv : list Z),
mk_base n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (m_refuse mcc (line + 1) false, Some gi) line rest = mf_final v ->
mf_at B v Wc regs1 memc mdc MK_REFUSE.

End e.
End f.
End d.
