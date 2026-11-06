(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): the inner cuts of segment S_MF_KMOD
   (KMODEL 0x86840 -> KIGN 0x86968 or KDONE 0x86c1c; the image-B m_file segment table section 8, the image-B m_file cut map
   section 4), in the form of lib/B/Prog/m_file_m.v's cut statements. Statement text only. A walk lane of
   the image-B m_file-family owner's G2B. The image-B twin of the image-A m_file-family lane's lib/A/Prog/m_file_s_kmod_m.v (commit
   c1e1a58468c5): image B calls fold (no inline loop), so its inner cuts are the call returns.

   What the piece does (the neutral listing of m_file in image B lines 450-483, 692-696, 735-738, 886):
     0x86840 a0 = 208(s1) = k, a2 = "model" (0x21220, listing object 19), a1 = s5 = kl; 0x86850 jal ieq
     0x86854 beqz a0 -> KIGN 0x86968 ("model" missed)
     0x86858 a0 = 192(s1) = v, a3 = 24, a1 = s10 = vl, s4 = 144(s1) = low = FB + 32, a2 = s4; 0x8686c jal fold
     0x86870 s5 = ln; a0 = low, a1 = ln; 0x8687c jal fuzz_catalogue_row
     0x86880 beqz a0 -> 0x86c08 (no row)
     0x86884 the UBSan trap 0x8688c (136(s1) = cur & 3 <> 0 -> unimp 0x86e84; not taken: cur = c + 256 gi, c mod 16
             = 0); s4 = 136(s1) = g, a0 = g + 36, a2 = ln + 1, a1 = 144(s1) = low; 0x868a0 jal checked_memcpy
     0x868a4 the check of g->model_set (store4 g + 32: shadow load 0x868b0, `bnez` to the slow path 0x86cb4-0x86cc0,
             error path 0x86f10, not reached), 0x868bc g->model_set = 1, 0x868c0 s9 = 112(s1) = c, `j` 0x86c18
     0x86c08 s9 = 112(s1) = c, a0 = c, a1 = s11 = line + 1; 0x86c14 jal m_refuse
     0x86c18 s4 = 511 -> KDONE 0x86c1c
   THE INNER CUTS (B pc; listing offset = AF_m_file + (pc - 0x86140)):
     MK_IRET   0x86854 (+0x714)  ieq's return: a0 = b2z (ieq k "model")
     MK_FRET   0x86870 (+0x730)  fold's return: a0 = ln = |h_fold v 24|, low.i = h_fold v 24 ++ [0], s4 = low
     MK_RRET   0x86880 (+0x740)  fuzz_catalogue_row's return: a0 = cat_ptr catA (cat_row (h_fold v 24)), s5 = ln
     MK_CRET   0x868a4 (+0x764)  checked_memcpy's return: g->model = low and its NUL (the block holds the entry
                                 with mkt_set_model low), s4 = g
     MK_REFUSE 0x86c08 (+0xac8)  m_refuse of the line (no catalogue row; also S_MF_KIGNP's bad value)
     MK_LI     0x86c18 (+0xad8)  `li s4,511` before KDONE (KDONE's state without s4)
   At each the K-cut state of m_file_m.v's MF_KAT_stmt holds (mk_base) with the key no longer needed: cur = Some gi,
   low.i in scope (MF_LOW_ON), the next line's address in 152(s1), s11 = line + 1. The model equation is the K cut's
   with ieq k "role" = false and ieq k "model" = true (mf_kmod_t.v mkt_disp_model: mk_disp = mk_mod), the branch on
   the row taken at MK_REFUSE (None) and MK_CRET (Some). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m mf_kmod_t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================================== the inner cut points ===================================== *)
Definition MK_IRET : Z := AF_m_file + 0x714.     (* 0x86854, ieq's return *)
Definition MK_FRET : Z := AF_m_file + 0x730.     (* 0x86870, fold's return *)
Definition MK_RRET : Z := AF_m_file + 0x740.     (* 0x86880, fuzz_catalogue_row's return *)
Definition MK_CRET : Z := AF_m_file + 0x764.     (* 0x868a4, checked_memcpy's return *)
Definition MK_REFUSE : Z := AF_m_file + 0xac8.   (* 0x86c08, m_refuse of the line *)
Definition MK_LI : Z := AF_m_file + 0xad8.       (* 0x86c18, `li s4,511` before KDONE *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the state every inner cut has: the K cut's (MF_KAT_stmt) without the key and the value, s11 = line + 1 *)
Definition mk_base (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
(memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc /\ mf_cells v lyc pos memc Wc (Some gi) /\
mf_regs_at B v lyc pos regs1 /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc (Some gi) line p rest /\
mf_np v memc Wc (mf_next p rest) /\ getr regs1 27 = w64 (line + 1).

(* 0x86854, ieq's return: the K cut's key and value facts, a0 = b2z (ieq k "model") *)
Definition MK_IRET_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
mk_base n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ->
mk_kv rest ok kl ov vl k vv -> Forall (fun w => ieq k w = false) [S_role] ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
mf_slot v memc Wc 208 (p + Z.of_nat ok) -> getr regs1 21 = w64 (Z.of_nat kl) ->
mf_slot v memc Wc 192 (p + Z.of_nat ov) -> getr regs1 26 = w64 (Z.of_nat vl) ->
getr regs1 10 = w64 (seg_spec.b2z (ieq k S_model)) ->
mf_at B v Wc regs1 memc mdc MK_IRET.

(* 0x86870, fold's return: low.i holds the folded value and its NUL; a0 = ln, s4 = low; the value's bytes are
   nonzero bytes (it lies in the line, before the text's NUL) *)
Definition MK_FRET_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (vv : list Z),
mk_base n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ->
mf_fin (mk_mod mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
~ In 0 vv -> Forall (fun b => 0 <= b < 256) vv ->
sa_zs (rdW Wc memc) (frame_addr lyc 1 pos + 32) (h_fold vv 24 ++ [0]) ->
getr regs1 10 = w64 (Z.of_nat (length (h_fold vv 24))) -> getr regs1 20 = w64 (frame_addr lyc 1 pos + 32) ->
mf_at B v Wc regs1 memc mdc MK_FRET.

(* 0x86880, fuzz_catalogue_row's return: a0 = &fuzz_catalogue[r] or NULL, s5 = ln *)
Definition MK_RRET_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (vv : list Z),
mk_base n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ->
mf_fin (mk_mod mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
~ In 0 vv -> Forall (fun b => 0 <= b < 256) vv ->
sa_zs (rdW Wc memc) (frame_addr lyc 1 pos + 32) (h_fold vv 24 ++ [0]) ->
getr regs1 21 = w64 (Z.of_nat (length (h_fold vv 24))) ->
getr regs1 10 = w64 (seg_spec.cat_ptr SegInstB.catA (cat_row (h_fold vv 24))) ->
mf_at B v Wc regs1 memc mdc MK_RRET.

(* 0x868a4, checked_memcpy's return: the block holds mcc with g->model = low (mkt_set_model low), s4 = g; the
   model equation is the found row's *)
Definition MK_CRET_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (low : list Z),
mk_base n v lyc Sc Wc regs1 memc mdc pos (m_upd mcc gi (mkt_set_model low)) gi line p rest ->
(length low < 24)%nat -> ~ In 0 low -> Forall (fun b => 0 <= b < 256) low ->
mf_fin (m_upd mcc gi (ms_with_model low), Some gi) line rest = mf_final v ->
getr regs1 20 = w64 (seg_spec.mseg_addr (mv_c v) gi) ->
mf_at B v Wc regs1 memc mdc MK_CRET.

(* 0x86c08, m_refuse of the line *)
Definition MK_REFUSE_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z),
mk_base n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ->
mf_fin (m_refuse mcc (line + 1) false, Some gi) line rest = mf_final v ->
mf_at B v Wc regs1 memc mdc MK_REFUSE.

(* 0x86c18, `li s4,511`: KDONE's statement (m_file_m.v MF_KDONE_stmt) without s4 *)
Definition MK_LI_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
mf_np v memc Wc p -> getr regs1 27 = w64 line ->
mf_at B v Wc regs1 memc mdc MK_LI.

End e.
End f.
End d.

(* each inner cut at every FP state (m_refuse returns at the FP state its snprintf calls leave) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Definition MK_IRET_F (n : nat) : Prop := forall fx0 : YK11.FPState, MK_IRET_stmt (fx := fx0) B n.
Definition MK_FRET_F (n : nat) : Prop := forall fx0 : YK11.FPState, MK_FRET_stmt (fx := fx0) B n.
Definition MK_RRET_F (n : nat) : Prop := forall fx0 : YK11.FPState, MK_RRET_stmt (fx := fx0) B n.
Definition MK_CRET_F (n : nat) : Prop := forall fx0 : YK11.FPState, MK_CRET_stmt (fx := fx0) B n.
Definition MK_REFUSE_F (n : nat) : Prop := forall fx0 : YK11.FPState, MK_REFUSE_stmt (fx := fx0) B n.
Definition MK_LI_F (n : nat) : Prop := forall fx0 : YK11.FPState, MK_LI_stmt (fx := fx0) B n.
End i.
End h.
End g.
