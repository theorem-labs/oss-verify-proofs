(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths, module names and numbers changed; 807 of its 905 lines of code are new or changed and 749 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/CheckTable.v; 352 of its 384 lines of code are new or changed and 873 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacPortsParse ClassifyCore.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed RcParse RcLeaf disco_classify_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition CLS_CHK_NEED : Z := 16 + ESTACK.

Definition PC_R1 : Z := AF_classify_core + 0x15c.
Definition PC_R2 : Z := AF_classify_core + 0x1cc.
Definition PC_SW : Z := AF_classify_core + 0x210.
Definition PC_ROLE : Z := AF_classify_core + 0x2a8.
Definition PC_R3 : Z := AF_classify_core + 0x418.
Definition PC_X : Z := AF_classify_core + 0x4f4.

Definition CLS_SW_ARMS : list Z := [0x2a0; 0x2a8; 0x2a8; 0x2a8; 0x63c; 0x2a8; 0x26c; 0x64c; 0x26c].
Definition CLS_RECIP : Z := (2 ^ 69 + 35) / 36.

Definition cls_spills : list (Z * Z) :=
[(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56); (22, -64); (23, -72);
 (24, -80); (25, -88); (26, -96); (27, -104)].

Definition PAT_A : list Z :=
[241; 241; 241; 241; 0; 0; 0; 0; 4; 242; 242; 242; 242; 242; 248; 248; 243; 243; 243; 243;
 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Definition PAT_B : list Z :=
[241; 241; 241; 241; 0; 0; 0; 0; 4; 242; 242; 242; 242; 242; 0; 4; 243; 243; 243; 243;
 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].

Definition cls_S1 (sp : Z) : Z := 32 * ((sp - 160) / 32).

Definition cls_O_Q (F : list byte) (len : Z) : list byte :=
disco_classify_c.src F ++ [CtrlParsed.zb 0; CtrlParsed.zb 0]
++ Mem.le4 (Z_to_bv 64 (disco_classify_c.role F (disco_classify_c.dkind F len)))
++ [CtrlParsed.zb 0; CtrlParsed.zb 0; CtrlParsed.zb 0]
++ [CtrlParsed.zb 0; CtrlParsed.zb (disco_classify_c.slots F); CtrlParsed.zb 0; CtrlParsed.zb 0; CtrlParsed.zb 0]
++ [CtrlParsed.zb 0; CtrlParsed.zb 0; CtrlParsed.zb 0; CtrlParsed.zb 0].

Definition cls_O_ROLE (F : list byte) : list byte :=
disco_classify_c.src F ++ repeat (CtrlParsed.zb 0) 18.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Record ccx := mkCCX {
  x_fq : YK11.FPState; x_STK : Z; x_sp0 : Z; x_FP : list (Z * Z); x_ly : alayout; x_S : astate;
  x_W0 : world SEGS; x_mem0 : word -> option byte; x_md0 : Model; x_own : list (Z * Z);
  x_lyc : alayout; x_Sc : astate; x_W : world SEGS; x_memc : word -> option byte; x_mdc : Model; x_k : Z;
  x_regs : bvmap 5 word; x_ch : list (Z * Z * Z);
  x_lk : Z; x_f : Z; x_len : Z; x_u : Z; x_o : Z;
  x_FB : list byte; x_U : list byte; x_OB : list byte; x_L : option (list byte) }.

Definition cSP (cx : ccx) : Z := spZ (x_regs cx).
Definition cS1 (cx : ccx) : Z := cls_S1 (cSP cx).
Definition cK (cx : ccx) : Z := disco_classify_c.dkind (x_FB cx) (x_len cx).
Definition cPS (cx : ccx) : list byte := snd (RcParse.ctrlparse (x_len cx) (x_FB cx)).
Definition cRet (cx : ccx) : Z := disco_classify_c.cm_ret (x_FB cx) (x_len cx) (x_U cx) (x_L cx).
Definition cOut (cx : ccx) : list byte := disco_classify_c.cm_out (x_FB cx) (x_len cx) (x_U cx) (x_L cx) (x_OB cx).
Definition cLock (cx : ccx) : option (list byte) := disco_classify_c.cm_lock (x_FB cx) (x_len cx) (x_U cx) (x_L cx).
Definition cBS (cx : ccx) : list byte := CtrlParsed.fld (x_FB cx) 18 20.

Section h.
Variable B : asyms.

Definition cF (cx : ccx) (fpos : Z) : Z := frame_addr (x_lyc cx) 2 fpos.
Definition cFL (cx : ccx) (fpos : Z) : Z := flag_addr (x_lyc cx) 2 fpos.

Definition cls_pre (cx : ccx) : Prop :=
let fq := x_fq cx in let STK := x_STK cx in let sp0 := x_sp0 cx in let FP := x_FP cx in
let ly := x_ly cx in let S := x_S cx in let W0 := x_W0 cx in let mem0 := x_mem0 cx in let md0 := x_md0 cx in
let own := x_own cx in let lyc := x_lyc cx in let Sc := x_Sc cx in let W := x_W cx in let memc := x_memc cx in
let mdc := x_mdc cx in let k := x_k cx in let regs := x_regs cx in let ch := x_ch cx in
let lk := x_lk cx in let f := x_f cx in let len := x_len cx in let u := x_u cx in let o := x_o cx in
let FB := x_FB cx in let U := x_U cx in let OB := x_OB cx in let L := x_L cx in
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 lk /\ getr regs 11 = w64 f /\ getr regs 12 = w64 len /\
getr regs 13 = w64 u /\ getr regs 14 = w64 o /\
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - CLS_STK /\ spZ regs <= sp0 /\
spZ regs + 32 <= ly_top lyc /\
Z.of_nat (length (frames Sc)) <= CLS_DEPTH /\
0 <= len < 2 ^ 64 /\
length FB = 50%nat /\ length U = 6%nat /\ length OB = 24%nat /\
(50 <= len -> 0 < f /\ cls_read W memc (spZ regs) f 50 /\ cls_sep B lyc Sc f 50 /\
  garr8 SEGS (mrestrict (w_H W) memc) f (cls_bytes FB)) /\
cls_read W memc (spZ regs) u 6 /\ cls_sep B lyc Sc u 6 /\
garr8 SEGS (mrestrict (w_H W) memc) u (cls_bytes U) /\
0 < o /\ o mod 4 = 0 /\
cls_read W memc (spZ regs) o 24 /\
garr8 SEGS (mrestrict (w_H W) memc) o (cls_bytes OB) /\
cls_write B STK sp0 FP ly S lyc Sc own o 24 /\
(o + 24 <= ly_stk_lo lyc \/ ly_stk_hi lyc <= o) /\
(match L with
 | None => lk = 0
 | Some Lb => 0 < lk /\ lk mod 4 = 0 /\ length Lb = 12%nat /\
   cls_read W memc (spZ regs) lk 12 /\
   garr8 SEGS (mrestrict (w_H W) memc) lk (cls_bytes Lb) /\
   cls_write B STK sp0 FP ly S lyc Sc own lk 12 /\
   (lk + 12 <= ly_stk_lo lyc \/ ly_stk_hi lyc <= lk)
 end) /\
(o + 24 <= u \/ u + 6 <= o) /\
(50 <= len -> o + 24 <= f \/ f + 50 <= o) /\
(match L with
 | None => True
 | Some _ => (lk + 12 <= o \/ o + 24 <= lk) /\ (lk + 12 <= u \/ u + 6 <= lk) /\
   (50 <= len -> lk + 12 <= f \/ f + 50 <= lk)
 end).

Definition cls_Q (cx : ccx) : world SEGS -> config -> Prop :=
tcls_post B (x_fq cx) (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_k cx) (x_regs cx)
  (x_lk cx) (x_o cx) (x_len cx) (x_FB cx) (x_U cx) (x_OB cx) (x_L cx).

Lemma tcls_entry_of_pre : forall a,
(forall cx, cls_pre cx ->
  SRr SEGS (x_W cx) (cfg_at (fx := x_fq cx) SEGS a (x_regs cx) (x_memc cx) (x_mdc cx)) (cls_Q cx)) ->
tcls_entry B a.
Proof.
intros a H. unfold tcls_entry.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch lk f len u o FB U OB L.
intros.
exact (H (mkCCX fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch lk f len u o FB U OB L)
  ltac:(unfold cls_pre; cbn; repeat (first [assumption | split]))).
Qed.

Definition cls_cut (cx : ccx) (fpos pc : Z) (RV : list (Z * Z)) (O3 : list byte) (L3 : option (list byte))
(SHP : list Z) (PS : option (list byte)) (LS : bool)
(W3 : world SEGS) (ly3 : alayout) (S3 : astate) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
: Prop :=
let F := cF cx fpos in let SP := cSP cx in let S1 := cS1 cx in
let m := mrestrict (w_H W3) mem3 in
ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  ((2, fpos) :: x_own cx) ly3 S3 W3 mem3 md3 (x_k cx) /\
frames S3 = (2, fpos) :: frames (x_Sc cx) /\ ~ In (2, fpos) (frames (x_Sc cx)) /\
Permutation (ablocks B ly3 S3) (ablocks B (x_lyc cx) (x_Sc cx)) /\
frame_addr ly3 2 fpos = F /\ flag_addr ly3 2 fpos = cFL cx fpos /\
tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W3 mem3 SP (x_lk cx) (x_o cx) (x_L cx) /\
getr regs3 2 = w64 S1 /\ getr regs3 3 = getr (x_regs cx) 3 /\ getr regs3 4 = getr (x_regs cx) 4 /\
getr regs3 8 = w64 SP /\ getr regs3 9 = w64 S1 /\ getr regs3 18 = w64 F /\ getr regs3 19 = w64 F /\
getr regs3 20 = w64 (-8) /\ getr regs3 27 = w64 (SHADOW_OFF + F / 8) /\
Forall (fun rv => getr regs3 (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV /\
Forall (fun p => val_mem SEGS m (SP + snd p) 8 (bv_unsigned (getr (x_regs cx) (Z_to_bv 5 (fst p))))) cls_spills /\
val_mem SEGS m (S1 + 16) 8 (x_o cx) /\ val_mem SEGS m (S1 + 24) 8 (x_f cx) /\ val_mem SEGS m (S1 + 48) 8 F /\
(LS = true -> val_mem SEGS m (S1 + 8) 8 (x_len cx)) /\
length SHP = 32%nat /\ garr8 SEGS m (SHADOW_OFF + F / 8) SHP /\
val_mem SEGS m (F + 248) 8 (cFL cx fpos) /\
(match PS with Some P => length P = 36%nat /\ garr8 SEGS m (F + 32) (cls_bytes P) | None => True end) /\
length O3 = 24%nat /\ garr8 SEGS m (x_o cx) (cls_bytes O3) /\
(match x_L cx, L3 with
 | None, None => True
 | Some _, Some Lb => length Lb = 12%nat /\ garr8 SEGS m (x_lk cx) (cls_bytes Lb)
 | _, _ => False
 end).

Definition cls_at_P (cx : ccx) (fpos : Z) W3 ly3 S3 regs3 mem3 md3 : Prop :=
let F := cF cx fpos in
cls_cut cx fpos AF_reac_ctrl_parse
  [(1, BASE + PC_R1); (10, x_f cx); (11, x_len cx); (12, F + 32);
   (21, SHADOW_OFF); (22, F + 32); (23, x_f cx); (24, x_lk cx); (25, x_len cx); (26, x_u cx)]
  (x_OB cx) (x_L cx) PAT_A None false W3 ly3 S3 regs3 mem3 md3.

Definition cls_at_R1 (cx : ccx) (fpos : Z) W3 ly3 S3 regs3 mem3 md3 : Prop :=
let F := cF cx fpos in
cls_cut cx fpos PC_R1
  [(10, cK cx); (21, SHADOW_OFF); (22, F + 32); (23, x_f cx); (24, x_lk cx); (25, x_len cx); (26, x_u cx)]
  (x_OB cx) (x_L cx) PAT_A (Some (cPS cx)) false W3 ly3 S3 regs3 mem3 md3.

Definition cls_at_K (cx : ccx) (fpos : Z) W3 ly3 S3 regs3 mem3 md3 : Prop :=
let F := cF cx fpos in
cK cx <> 0 /\ cK cx <> 1 /\ CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx) = false /\
cls_cut cx fpos AF_reac_ctrl_checksum_verify
  [(1, BASE + PC_R2); (10, x_f cx); (21, SHADOW_OFF); (22, F + 32); (23, -1); (24, x_lk cx); (25, F + 36); (26, x_u cx)]
  (x_OB cx) (x_L cx) PAT_A (Some (cPS cx)) true W3 ly3 S3 regs3 mem3 md3.

Definition cls_at_R2 (cx : ccx) (fpos : Z) W3 ly3 S3 regs3 mem3 md3 : Prop :=
let F := cF cx fpos in
cK cx <> 0 /\ cK cx <> 1 /\ CtrlParsed.bytes_eqb (disco_classify_c.src (x_FB cx)) (x_U cx) = false /\
cls_cut cx fpos PC_R2
  [(10, if disco_classify_c.fsum (x_FB cx) =? 0 then 0 else -1);
   (21, SHADOW_OFF); (22, F + 32); (23, -1); (24, x_lk cx); (25, F + 36); (26, x_u cx)]
  (x_OB cx) (x_L cx) PAT_A (Some (cPS cx)) true W3 ly3 S3 regs3 mem3 md3.

Definition cls_at_SW (cx : ccx) (fpos : Z) W3 ly3 S3 regs3 mem3 md3 : Prop :=
let F := cF cx fpos in
cRet cx = 0 /\
cls_cut cx fpos PC_SW [(21, SHADOW_OFF); (22, F + 32); (25, F + 36)]
  (x_OB cx) (cLock cx) PAT_A (Some (cPS cx)) true W3 ly3 S3 regs3 mem3 md3.

Definition cls_at_ROLE (cx : ccx) (fpos : Z) W3 ly3 S3 regs3 mem3 md3 : Prop :=
let F := cF cx fpos in
cRet cx = 0 /\
cls_cut cx fpos PC_ROLE
  [(11, disco_classify_c.role (x_FB cx) (cK cx)); (21, x_len cx); (22, F + 32); (23, SHADOW_OFF); (24, x_o cx); (25, F + 36)]
  (cls_O_ROLE (x_FB cx)) (cLock cx) PAT_A None false W3 ly3 S3 regs3 mem3 md3.

Definition cls_at_Q (cx : ccx) (fpos : Z) W3 ly3 S3 regs3 mem3 md3 : Prop :=
let F := cF cx fpos in
cRet cx = 0 /\
cls_cut cx fpos AF_reac_ports_parse
  [(1, BASE + PC_R3); (10, x_f cx + 18); (11, F + 112);
   (21, x_len cx); (22, F + 112); (23, SHADOW_OFF); (24, x_o cx); (25, F + 36)]
  (cls_O_Q (x_FB cx) (x_len cx)) (cLock cx) PAT_B None false W3 ly3 S3 regs3 mem3 md3.

Definition cls_at_R3 (cx : ccx) (fpos : Z) W3 ly3 S3 regs3 mem3 md3 : Prop :=
let F := cF cx fpos in
cRet cx = 0 /\
cls_cut cx fpos PC_R3
  [(10, if RcLeaf.ports_ok (x_f cx + 18) (F + 112) (cBS cx) then 0 else -1);
   (21, x_len cx); (22, F + 112); (23, SHADOW_OFF); (24, x_o cx); (25, F + 36)]
  (cls_O_Q (x_FB cx) (x_len cx)) (cLock cx) PAT_B None false W3 ly3 S3 regs3 mem3 md3 /\
(RcLeaf.ports_ok (x_f cx + 18) (F + 112) (cBS cx) = true ->
  val_mem SEGS (mrestrict (w_H W3) mem3) (F + 112) 4 (4 * RcLeaf.n_in (cBS cx)) /\
  val_mem SEGS (mrestrict (w_H W3) mem3) (F + 116) 4 (4 * RcLeaf.n_out (cBS cx))).

Definition cls_at_X (cx : ccx) (fpos : Z) W3 ly3 S3 regs3 mem3 md3 : Prop :=
cls_cut cx fpos PC_X [(23, cRet cx)] (cOut cx) (cLock cx) PAT_A None false W3 ly3 S3 regs3 mem3 md3.

Definition cls_from (pc : Z)
(P : ccx -> Z -> world SEGS -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) : Prop :=
forall cx fpos W3 ly3 S3 regs3 mem3 md3,
cls_pre cx -> P cx fpos W3 ly3 S3 regs3 mem3 md3 ->
SRr SEGS W3 (cfg_at (fx := x_fq cx) SEGS (BASE + pc) regs3 mem3 md3) (cls_Q cx).

Definition cls_from_P : Prop := cls_from AF_reac_ctrl_parse cls_at_P.
Definition cls_from_R1 : Prop := cls_from PC_R1 cls_at_R1.
Definition cls_from_K : Prop := cls_from AF_reac_ctrl_checksum_verify cls_at_K.
Definition cls_from_R2 : Prop := cls_from PC_R2 cls_at_R2.
Definition cls_from_SW : Prop := cls_from PC_SW cls_at_SW.
Definition cls_from_ROLE : Prop := cls_from PC_ROLE cls_at_ROLE.
Definition cls_from_Q : Prop := cls_from AF_reac_ports_parse cls_at_Q.
Definition cls_from_R3 : Prop := cls_from PC_R3 cls_at_R3.
Definition cls_from_X : Prop := cls_from PC_X cls_at_X.

Definition tcallee_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
(W2 : world SEGS) (mem2 : word -> option byte) (slo shi : Z) (Er : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ Er a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ Er (b + i) ->
  aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  ~ Er a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
  apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, slo <= a < shi -> apresent (w_H W2) mem2 a).

Definition tparse_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (q len : Z) (FB : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fq) k) /\
  (@YK11.fp_csr fx' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
  aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  getr regs2 10 = w64 (fst (RcParse.ctrlparse len FB)) /\
  garr8 SEGS (mrestrict (w_H W2) mem2) q (cls_bytes (snd (RcParse.ctrlparse len FB))) /\
  tcallee_kept lyc Sc W memc W2 mem2 (spZ regs - CLS_PARSE_NEED) (spZ regs) (fun a => q <= a < q + 36).

Definition tparse_need : Prop :=
forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
  (p len q : Z) (FB : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 p -> getr regs 11 = w64 len -> getr regs 12 = w64 q ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CLS_PARSE_NEED -> spZ regs <= sp0 ->
spZ regs + 32 <= ly_top lyc ->
Z.of_nat (length (frames Sc)) <= CLS_DEPTH + 1 ->
0 <= len < 2 ^ 64 -> length FB = 50%nat ->
(50 <= len -> 0 < p /\ p + 50 <= 2 ^ 47 /\ amem_range p 50 /\ off_img p 50 /\
  (p + 50 <= kLowShadowBeg \/ kHighMemBeg <= p) /\
  (spZ regs <= p \/ p + 50 <= spZ regs - CLS_PARSE_NEED) /\
  (forall a, p <= a < p + 50 -> apresent (w_H W) memc a) /\
  cls_sep B lyc Sc p 50 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 50 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) p 50 /\
  garr8 SEGS (mrestrict (w_H W) memc) p (cls_bytes FB) /\
  (q + 36 <= p \/ p + 50 <= q)) ->
q mod 32 = 0 -> 4096 <= q -> q + 36 <= 2 ^ 47 -> amem_range q 36 -> off_img q 36 ->
(q + 36 <= kLowShadowBeg \/ kHighMemBeg <= q) ->
q + 36 <= alloc_ceiling ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 36 ->
shadow_hull_vis (aview SEGS (w_H W) memc) q 36 ->
(forall a, q <= a < q + 36 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_ctrl_parse) regs memc mdc)
  (tparse_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs q len FB).

Definition tchk_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (FB : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fq) k) /\
  (@YK11.fp_csr fx' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
  aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  getr regs2 10 = w64 (if disco_classify_c.fsum FB =? 0 then 0 else -1) /\
  tcallee_kept lyc Sc W memc W2 mem2 (spZ regs - CLS_CHK_NEED) (spZ regs) (fun _ => False).

Definition tchk_need : Prop :=
forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
  (p : Z) (FB : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 p ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CLS_CHK_NEED -> spZ regs <= sp0 ->
length FB = 50%nat ->
0 < p -> p + 50 <= 2 ^ 47 -> amem_range p 50 -> off_img p 50 ->
(p + 50 <= kLowShadowBeg \/ kHighMemBeg <= p) ->
(spZ regs <= p \/ p + 50 <= spZ regs - CLS_CHK_NEED) ->
(forall a, p <= a < p + 50 -> apresent (w_H W) memc a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 50 ->
shadow_hull_vis (aview SEGS (w_H W) memc) p 50 ->
garr8 SEGS (mrestrict (w_H W) memc) p (cls_bytes FB) ->
SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_ctrl_checksum_verify) regs memc mdc)
  (tchk_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FB).

Definition cls_addr (p n : Z) : Prop :=
0 <= p /\ p + n <= 2 ^ 47 /\ amem_range p n /\ off_img p n /\ (p + n <= kLowShadowBeg \/ kHighMemBeg <= p).

Definition cls_live (W3 : world SEGS) (mem3 : word -> option byte) (p n : Z) : Prop :=
(forall a, p <= a < p + n -> apresent (w_H W3) mem3 a) /\
range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF p n /\
shadow_hull_vis (aview SEGS (w_H W3) mem3) p n.

Definition cls_obj_ok (cx : ccx) (fpos : Z) (W3 : world SEGS) (mem3 : word -> option byte) (p n : Z) : Prop :=
let F := cF cx fpos in
cls_addr p n /\ cls_live W3 mem3 p n /\ (p + n <= F \/ F + 256 <= p) /\
(cSP cx <= p \/ p + n <= cSP cx - CLS_STK).

Definition cls_now_ok : Prop :=
forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3,
cls_pre cx -> cls_cut cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
let F := cF cx fpos in let FL := cFL cx fpos in let m := mrestrict (w_H W3) mem3 in
let own' := (2, fpos) :: x_own cx in
(4096 <= F /\ F + 256 <= alloc_ceiling /\ F mod 32 = 0 /\ zone2 F 256 /\ in_app F 256 /\
 (forall a, F <= a < F + 256 -> apresent (w_H W3) mem3 a) /\
 (forall i, 0 <= i < 32 -> apresent (w_H W3) mem3 (SHADOW_OFF + F / 8 + i)) /\
 4096 <= FL /\ zone2 FL 1 /\ FL < alloc_ceiling /\ apresent (w_H W3) mem3 FL /\
 aowned B ly3 S3 FL /\ ~ (F <= FL < F + 256) /\
 (forall b n, In (b, n) (ablocks B ly3 S3) -> b + req_size n <= F \/ F + 256 <= b) /\
 (forall c p, In (c, p) (frames (x_Sc cx)) -> frame_addr ly3 c p + fs_frame_bytes c <= F \/ F + 256 <= frame_addr ly3 c p)) /\
(50 <= x_len cx -> garr8 SEGS m (x_f cx) (cls_bytes (x_FB cx)) /\ cls_obj_ok cx fpos W3 mem3 (x_f cx) 50) /\
garr8 SEGS m (x_u cx) (cls_bytes (x_U cx)) /\ cls_obj_ok cx fpos W3 mem3 (x_u cx) 6 /\
cls_obj_ok cx fpos W3 mem3 (x_o cx) 24 /\ 4096 <= x_o cx /\ x_o cx + 24 <= alloc_ceiling /\
(forall a, x_o cx <= a < x_o cx + 24 ->
  awr_byte (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly3 S3) ly3 own' a) /\
(match x_L cx with
 | None => True
 | Some _ => cls_obj_ok cx fpos W3 mem3 (x_lk cx) 12 /\ 4096 <= x_lk cx /\ x_lk cx + 12 <= alloc_ceiling /\
   (forall a, x_lk cx <= a < x_lk cx + 12 ->
     awr_byte (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly3 S3) ly3 own' a)
 end).

Definition cls_achain_ok : Prop :=
forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3,
cls_pre cx -> cls_cut cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
exists ch, achain ly3 (aview SEGS (w_H W3) mem3) (cS1 cx) (cSP cx) ch.

Definition cls_kept_step_ok : Prop :=
forall cx fpos (W3 : world SEGS) ly3 S3 (mem3 : word -> option byte) md3 (mem4 : word -> option byte) (Wr : Z -> Prop),
cls_pre cx -> AR SEGS B ly3 S3 W3 mem3 md3 ->
frames S3 = (2, fpos) :: frames (x_Sc cx) -> ~ In (2, fpos) (frames (x_Sc cx)) ->
Permutation (ablocks B ly3 S3) (ablocks B (x_lyc cx) (x_Sc cx)) ->
frame_addr ly3 2 fpos = cF cx fpos -> flag_addr ly3 2 fpos = cFL cx fpos ->
tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W3 mem3 (cSP cx) (x_lk cx) (x_o cx) (x_L cx) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a) ->
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem4 a) ->
(forall a, Wr a ->
  (cSP cx - CLS_STK <= a < cSP cx) \/ cls_wr (x_lk cx) (x_o cx) (x_L cx) a \/
  (cF cx fpos <= a < cF cx fpos + 256) \/
  (SHADOW_OFF + cF cx fpos / 8 <= a < SHADOW_OFF + cF cx fpos / 8 + 32) \/ a = cFL cx fpos) ->
tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W3 mem4 (cSP cx) (x_lk cx) (x_o cx) (x_L cx).

Definition cls_rom_ok : Prop :=
forall (H : word -> bool) (mem : word -> option byte),
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 36)) 8 CLS_RECIP /\
(forall i, (i < 9)%nat ->
  val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 35) + 4 * Z.of_nat i) 4
    ((BASE + AF_classify_core + nth i CLS_SW_ARMS 0 - VAL (A_OBJ 35)) mod 2 ^ 32)).

End h.
End f.
End d.
