(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 876d0cb3d0d; for reac-pw/fuzz_headamp image A, proving HPgSeg's hs_piece_W6a_disp_stmt / hs_piece_W6a_cases_stmt: module paths and the rs_ / rl_ / rm_ prefixes renamed to hs_ / hd_ / hm_, the cut lists of HPgSeg (headamp's hs_Kc, hs_L_pod, hs_L_D: the pod loop's cells R+0xa8 / 0xc0 / 0xc8 / 0xd8 / 0xe8 / 0xf8 / 0x118 by the plan's slot map), hs_pre at hi_shA, hd_seg_pre's conjunct order (pp's block from hd_fresh_block, the globals at conjunct 16, R mod 32), the frame for locals of class 4 (1024 bytes, 80 shadow bytes), the real frame of 0x1e0 bytes and hi_w1 = [(XF 0, 0x20, 0x138); (XShF, 0, 80); (XR, 0, 0x160)]. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the two piece lemmas of the
   walk piece "ent_build A" of LLVMFuzzerTestOneInput (0x80bc0), lib/A/HPgSeg.v's hs_piece_W6a_disp_stmt and
   hs_piece_W6a_cases_stmt at image A's segments, chained from the block lemmas of lib/A/HPgW6aBase.v.
   Proves no function (kind: segment lemma).

   THE DISPATCH (w6_disp). From the pod loop's head C (0x817a0): the head block (w6_head: [R+0xf8] := k, e's 13
   shadow granules := 0, the memset of e) and the kind block (w6_kind: the kind byte, kind % 10, the branch to case
   9 or the jump table) end at one of the switch's entries; there the state is the cut D of that kind (or D0E when
   no input is left). The cut's journal, frames, blocks and the bytes outside the callees' stack and hs_E1 come from
   the cut C through the two blocks' posts; the R cells, the registers and pp's image are kept (the head writes only
   [R - ESTACK, R), [R+0xf8, R+0x100), e and its shadow); e's shadow is the pattern hs_PJ and e holds 104 zeros.

   THE CASES 2 AND 3 (w6_cases). From the cut D of kind % 10 = 2 (3): the case's head block (w6_c2h / w6_c3h), on
   an odd m the fuzz_u32 read-ahead block (lib/A/HPgSteps.v), and the tail (w6_tail2 / w6_tail3) end at J with e
   holding Layout.ent_mem of Model.ent_build's pod of the turn's input. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSteps HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW6cKit HPgW6aBase HPgW6aHead HPgW6aKind.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW6aC2h HPgW6aC3h HPgW6aTail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== list tactics ======================================== *)
(* the location lists of the cuts, as literal lists *)
Ltac w6_unf := cbv [hs_L_pod hs_Rc hs_Rc0 hs_Kc hs_L_Dc hs_L_Dc0 hs_L_D app].
(* membership in a literal list *)
Ltac w6_mem := cbn [In]; repeat first [left; reflexivity | right].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ======================================== registers ======================================== *)
Definition w6_regok (clob : list (bv 5)) (r : Z) : bool :=
negb (bv_unsigned (Z_to_bv 5 r) =? 0) && negb (existsb (fun c => bv_eqb c (Z_to_bv 5 r)) clob).

Lemma w6_kept_bv : forall (regs regs' : bvmap 5 word) (clob : list (bv 5)) (q : bv 5),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) ->
negb (bv_unsigned q =? 0) && negb (existsb (fun c => bv_eqb c q) clob) = true ->
getr regs' q = getr regs q.
Proof.
intros regs regs' clob q K H. apply andb_prop in H as [H1 H2]. apply negb_true_iff in H1. apply negb_true_iff in H2.
apply K.
- apply Z.eqb_neq. exact H1.
- intros Hin. assert (E : existsb (fun c => bv_eqb c q) clob = true).
  { apply existsb_exists. exists q. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_eq. reflexivity. }
  congruence.
Qed.

Lemma w6_reg_kept : forall (regs regs' : bvmap 5 word) clob r,
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q clob -> getr regs' q = getr regs q) ->
w6_regok clob r = true -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof. intros regs regs' clob r K H. exact (w6_kept_bv regs regs' clob (Z_to_bv 5 r) K H). Qed.

Lemma w6_regZ : forall (regs : bvmap 5 word) (q : bv 5) r, bv_unsigned q = r -> getr regs (Z_to_bv 5 r) = getr regs q.
Proof. intros regs q r <-. rewrite (Z_to_bv_bv_unsigned 5 q). reflexivity. Qed.

(* an 8-byte cell holds v exactly when it holds v mod 2^64 *)
Lemma w6_val_mod : forall m a v, val_mem rsegs m a 8 (v mod 2 ^ 64) <-> val_mem rsegs m a 8 v.
Proof.
intros m a v. unfold val_mem.
assert (E : forall k, YO0f.le_byte (v mod 2 ^ 64) 8 k = YO0f.le_byte v 8 k).
{ intros k. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
split; intros H k Hk; specialize (H k Hk); [rewrite <- E | rewrite E]; exact H.
Qed.

(* ======================================== location lists ======================================== *)
Lemma w6_at_get : forall H mem regs e (L : list (hd_loc * Z)) l v,
hs_at rsegs H mem regs e L -> In (l, v) L -> hd_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v A Hin. unfold hs_at in A. rewrite Forall_forall in A. exact (A _ Hin). Qed.

Lemma w6_at_reg : forall H mem regs e (L : list (hd_loc * Z)) r v (q : bv 5),
hs_at rsegs H mem regs e L -> In (LReg r, v) L -> bv_unsigned q = r -> getr regs q = w64 v.
Proof.
intros H mem regs e L r v q A Hin Hq. rewrite <- (w6_regZ regs q r Hq).
exact (w6_at_get H mem regs e L (LReg r) v A Hin).
Qed.

Lemma w6_at_cell8 : forall H mem regs e (L : list (hd_loc * Z)) b o v,
hs_at rsegs H mem regs e L -> In (LCell b o, v) L -> val_mem rsegs (mrestrict H mem) (hd_xv e b + o) 8 v.
Proof. intros H mem regs e L b o v A Hin. apply w6_val_mod. exact (w6_at_get H mem regs e L (LCell b o) v A Hin). Qed.

Lemma w6_fsub : forall {X} (P : X -> Prop) (L L' : list X), Forall P L -> Forall (fun f => In f L \/ P f) L' -> Forall P L'.
Proof.
intros X P L L' HL H. rewrite Forall_forall in *. intros f Hf.
destruct (H f Hf) as [Hi|Hp]; [exact (HL f Hi) | exact Hp].
Qed.

(* a location list carried across a block that keeps every register outside clob and every byte outside Wr *)
Definition w6_side (clob : list (bv 5)) (Wr : Z -> Prop) (e : hd_env) (f : hd_loc * Z) : Prop :=
match fst f with
| LReg r => w6_regok clob r = true
| LCell b o => forall i, 0 <= i < 8 -> 0 <= hd_xv e b + o + i < 2 ^ 64 /\ ~ Wr (hd_xv e b + o + i)
end.
Lemma w6_atl_tr : forall (Wr : Z -> Prop) clob H mem H' mem' regs regs' e L,
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q clob -> getr regs' q = getr regs q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs H' mem' a = aview rsegs H mem a) ->
Forall (w6_side clob Wr e) L ->
hs_at rsegs H mem regs e L -> hs_at rsegs H' mem' regs' e L.
Proof.
intros Wr clob H mem H' mem' regs regs' e L K M C A. unfold hs_at in *.
apply (hm_atl_kept rsegs H mem H' mem' regs regs' e L A).
intros f Hf. rewrite Forall_forall in C. specialize (C f Hf). unfold w6_side in C.
destruct f as [[r|b o] v]; cbn [fst hm_keeps] in *.
- exact (w6_reg_kept regs regs' clob r K C).
- intros i Hi. destruct (C i Hi) as [Hr Hn]. exact (M _ Hr Hn).
Qed.

(* ======================================== the geometry of a cut ========================================
   R's frame above the ceiling with the callees' stack below it, the frame for locals F and its shadow and the
   block pp below the ceiling, apart from each other *)
Definition w6_geo (R F pp : Z) : Prop :=
alloc_ceiling + T_SEG_STK <= R /\ R + 0x1e0 <= 2 ^ 47 /\ kHighMemBeg <= R - T_SEG_STK /\
in_app F 1024 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\ 0 <= shadow_addr F /\ shadow_addr F + 128 <= alloc_ceiling /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\
4096 <= pp /\ pp + Layout.PP_SIZE <= alloc_ceiling /\
(pp + Layout.PP_SIZE <= shadow_addr F \/ shadow_addr F + 128 <= pp) /\
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp).

Lemma w6_hw_cell : forall R F pp o i, w6_geo R F pp ->
((0 <=? o) && (o + 8 <=? 0x1e0) && ((o + 8 <=? 0xf8) || (0x100 <=? o)))%bool = true -> 0 <= i < 8 ->
0 <= R + o + i < 2 ^ 64 /\ ~ w6_head_wr R F (R + o + i).
Proof.
intros R F pp o i G Hb Hi.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply orb_prop in H3.
unfold w6_geo, w6_head_wr, T_SEG_STK, ASTACK, ESTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & _).
destruct H3 as [H3|H3]; apply Z.leb_le in H3; lia.
Qed.

Lemma w6_R_cell : forall R F pp o i, w6_geo R F pp -> ((0 <=? o) && (o + 8 <=? 0x1e0))%bool = true -> 0 <= i < 8 ->
0 <= R + o + i < 2 ^ 64.
Proof.
intros R F pp o i G Hb Hi. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold w6_geo, T_SEG_STK, ASTACK in *. destruct G as (G1 & G2 & _ & _ & _ & _ & G7 & G8 & _). lia.
Qed.

Lemma w6_hw_fsh : forall R F pp i, w6_geo R F pp -> 0 <= i < 80 -> ~ (30 <= i < 43) ->
0 <= shadow_addr F + i < 2 ^ 64 /\ ~ w6_head_wr R F (shadow_addr F + i).
Proof.
intros R F pp i G Hi Hn. unfold w6_geo, w6_head_wr, T_SEG_STK, ASTACK, ESTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & G9 & _). lia.
Qed.

Lemma w6_hw_pp : forall R F pp i, w6_geo R F pp -> 0 <= i < Layout.PP_SIZE ->
0 <= pp + i < 2 ^ 64 /\ ~ w6_head_wr R F (pp + i).
Proof.
intros R F pp i G Hi. unfold w6_geo, w6_head_wr, T_SEG_STK, ASTACK, ESTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). unfold Layout.PP_SIZE in *. lia.
Qed.

Lemma w6_hw_shin : forall R F pp x, w6_geo R F pp -> 0 <= x < kHighMemEnd ->
~ (shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 80) ->
0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ w6_head_wr R F (shadow_of_addr SHADOW_OFF x).
Proof.
intros R F pp x G Hx Hn.
destruct G as (G1 & G2 & G3 & G4 & _).
pose proof (hm_shadow_band x Hx) as Hb.
pose proof (hm_shadow_not_app x F 1024 Hx G4) as Hna.
unfold kLowMemEnd, kHighMemBeg in Hb. unfold kHighMemBeg in G3.
split; [lia|].
unfold w6_head_wr, T_SEG_STK, ASTACK, ESTACK in *. intros [H|[H|[H|H]]]; [lia | lia | apply Hn; lia | apply Hna; lia].
Qed.

(* the image's first write range, piece by piece *)
Lemma w6_inw1 : forall e a,
(e_F e + 0x20 <= a < e_F e + 0x158) \/ (shadow_addr (e_F e) <= a < shadow_addr (e_F e) + 80) \/
(e_R e <= a < e_R e + 0x160) -> hd_inw e (hi_w1 headamp_himg_A) a.
Proof.
intros e a H. unfold hd_inw. cbn [hi_w1 headamp_himg_A].
destruct H as [H|[H|H]].
- apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
- apply Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia.
Qed.

(* what the head writes is in the callees' stack or in the image's first write range *)
Lemma w6_hw_E1 : forall e a, w6_head_wr (e_R e) (e_F e) a ->
(e_R e - T_SEG_STK <= a < e_R e) \/ hd_inw e (hi_w1 headamp_himg_A) a.
Proof.
intros e a H. unfold w6_head_wr in H.
destruct H as [H|[H|[H|H]]].
- left. unfold T_SEG_STK, ASTACK, ESTACK in *. lia.
- right. apply w6_inw1. right. right. lia.
- right. apply w6_inw1. right. left. lia.
- right. apply w6_inw1. left. lia.
Qed.

(* what the tail writes: e's first 12 bytes and [R+0x118, R+0x120) *)
Lemma w6_tw_E1 : forall e a, w6_tail_wr (e_R e) (e_F e) a -> hd_inw e (hi_w1 headamp_himg_A) a.
Proof.
intros e a H. unfold w6_tail_wr in H. apply w6_inw1.
destruct H as [H|H]; [left; lia | right; right; lia].
Qed.

Lemma w6_tw_cell : forall R F pp o i, w6_geo R F pp ->
((0 <=? o) && (o + 8 <=? 0x1e0) && ((o + 8 <=? 0x118) || (0x120 <=? o)))%bool = true -> 0 <= i < 8 ->
0 <= R + o + i < 2 ^ 64 /\ ~ w6_tail_wr R F (R + o + i).
Proof.
intros R F pp o i G Hb Hi.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply orb_prop in H3.
unfold w6_geo, w6_tail_wr, T_SEG_STK, ASTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & _).
destruct H3 as [H3|H3]; apply Z.leb_le in H3; lia.
Qed.

Lemma w6_tw_fsh : forall R F pp i, w6_geo R F pp -> 0 <= i < 80 ->
0 <= shadow_addr F + i < 2 ^ 64 /\ ~ w6_tail_wr R F (shadow_addr F + i).
Proof.
intros R F pp i G Hi. unfold w6_geo, w6_tail_wr, T_SEG_STK, ASTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & G9 & _). lia.
Qed.

Lemma w6_tw_pp : forall R F pp i, w6_geo R F pp -> 0 <= i < Layout.PP_SIZE ->
0 <= pp + i < 2 ^ 64 /\ ~ w6_tail_wr R F (pp + i).
Proof.
intros R F pp i G Hi. unfold w6_geo, w6_tail_wr, T_SEG_STK, ASTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). unfold Layout.PP_SIZE in *. lia.
Qed.

Lemma w6_tw_e : forall R F pp i, w6_geo R F pp -> 12 <= i < 104 ->
0 <= F + 0xf0 + i < 2 ^ 64 /\ ~ w6_tail_wr R F (F + 0xf0 + i).
Proof.
intros R F pp i G Hi. unfold w6_geo, w6_tail_wr, T_SEG_STK, ASTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & _). lia.
Qed.

Lemma w6_vb_range : forall R F pp, w6_geo R F pp -> 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64.
Proof.
intros R F pp G. destruct G as (G1 & G2 & _ & _ & _ & _ & _ & _ & _ & G10 & G11 & _).
unfold shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK, Layout.PP_SIZE in *.
pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound (pp + 0x4000) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
lia.
Qed.

(* a 4-byte cell holds v exactly when it holds v mod 2^32 *)
Lemma w6_val_mod32 : forall m a v, val_mem rsegs m a 4 (v mod 2 ^ 32) <-> val_mem rsegs m a 4 v.
Proof.
intros m a v. unfold val_mem.
assert (E : forall k, YO0f.le_byte (v mod 2 ^ 32) 4 k = YO0f.le_byte v 4 k).
{ intros k. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. reflexivity. }
split; intros H k Hk; specialize (H k Hk); [rewrite <- E | rewrite E]; exact H.
Qed.

(* the cursor and the suffix after the bytes a read consumed *)
Lemma w6_suffix_skip : forall rest r n, hs_suffix rest r -> hs_suffix rest (skipn n r).
Proof.
intros rest r n (j & Hj & ->). rewrite skipn_skipn.
destruct (Nat.le_gt_cases (n + j) (length rest)) as [Hle|Hgt].
- exists (n + j)%nat. split; [exact Hle | reflexivity].
- exists (length rest). split; [lia|]. rewrite !skipn_all2 by lia. reflexivity.
Qed.

Lemma w6_cur_skip : forall (cx : hs_scx rsegs) rest r n,
hs_cur rsegs cx rest (skipn n r) = hs_cur rsegs cx rest r + Z.of_nat (Nat.min n (length r)).
Proof. intros cx rest r n. unfold hs_cur. rewrite length_skipn. lia. Qed.

Lemma w6_cur_pos : forall (cx : hs_scx rsegs) rest (b : byte) r, hs_in rsegs cx rest -> hs_suffix rest (b :: r) ->
0 < hs_cur rsegs cx rest r - 1.
Proof.
intros cx rest b r HI (j & Hj & E). destruct HI as (Hleft & _ & _ & _ & _ & Hsrc & _).
assert (Hl : length (skipn j rest) = S (length r)) by (rewrite <- E; reflexivity).
rewrite length_skipn in Hl. unfold hs_cur. lia.
Qed.

(* Model.ent_build's cases 2 and 3: the int / float pod of m, with the fuzz_u32 read-ahead on an odd m *)
Lemma w6_ent_build : forall (c3 : bool) (b : byte) r, bv_unsigned b mod 10 = (if c3 then 3 else 2) ->
ent_build (b :: r) =
(Ent (if c3 then POD_FLOAT else POD_INT) 4
  (le32 (if Z.odd (fst (fuzz_u8 r)) then fst (fuzz_u32 (snd (fuzz_u8 r)))
         else if c3 then w6_float_even (fst (fuzz_u8 r)) else w6_int_even (fst (fuzz_u8 r)))),
 if Z.odd (fst (fuzz_u8 r)) then snd (fuzz_u32 (snd (fuzz_u8 r))) else snd (fuzz_u8 r)).
Proof.
intros c3 b r H. unfold ent_build.
change (fuzz_u8 (b :: r)) with (bv_unsigned b, r). cbv beta iota zeta.
rewrite H. destruct (fuzz_u8 r) as [m r1]. cbn [fst snd].
destruct c3; [change (Z.to_nat 3) with 3%nat | change (Z.to_nat 2) with 2%nat]; cbv beta iota;
destruct (Z.odd m); cbv beta iota.
- destruct (fuzz_u32 r1) as [v r2]. reflexivity.
- unfold w6_float_even. destruct (m / 2 =? 127); [reflexivity|]. destruct (m / 2 =? 126); reflexivity.
- destruct (fuzz_u32 r1) as [v r2]. reflexivity.
- reflexivity.
Qed.

Lemma w6_rs_pc_23 : forall (c3 : bool) kd, kd mod 10 = (if c3 then 3 else 2) -> hs_pc_D kd = (if c3 then W6_D3 else W6_D2).
Proof. intros c3 kd H. unfold hs_pc_D. rewrite H. destruct c3; reflexivity. Qed.

(* ======================================== pp's image ======================================== *)
Lemma w6_pc_ents_wf : forall sh ps es, Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) ->
Forall ent_wf es -> (length es <= 32)%nat ->
(length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps (Some es))).
Proof.
intros sh ps es Hk He Hes Hl. unfold pc_ents. cbn [pc_props pc_open].
destruct (first_params ps) as [[iv|es']|] eqn:E.
- split; [cbn; lia | constructor].
- unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
  apply find_some in F as [Hin _]. split.
  + rewrite Forall_forall in Hk. specialize (Hk kv Hin). rewrite E in Hk. exact Hk.
  + apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He.
- split; [exact Hl | exact Hes].
Qed.

Lemma w6_pp_len : forall sh ps es, hs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
intros sh ps es (_ & Hkv & Hae & Hlp) Hes Hle.
assert (Hpv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hkv]; intros kv [_ H]; exact H).
destruct (w6_pc_ents_wf sh ps es Hpv Hae Hes ltac:(lia)) as [Hn Hw].
unfold pc_image. cbn [pc_shape pc_props pc_open]. apply length_pp_image.
- destruct (pc_buf_len_open sh ps es Hpv Hae Hes) as [H _]. lia.
- exact Hn.
- eapply Forall_impl; [|exact Hw]. intros e (_ & H1 & H2). rewrite H1. lia.
Qed.

(* ======================================== kind % 10 and the switch's entries ======================================== *)
Lemma w6_case_pc_D : forall kd, w6_case_pc kd = hs_pc_D kd.
Proof.
intros kd. unfold w6_case_pc, hs_pc_D.
pose proof (Z.mod_pos_bound kd 10 ltac:(lia)) as Hm.
destruct jt_tgt_vals as (J0 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8).
assert (H : kd mod 10 = 0 \/ kd mod 10 = 1 \/ kd mod 10 = 2 \/ kd mod 10 = 3 \/ kd mod 10 = 4 \/
  kd mod 10 = 5 \/ kd mod 10 = 6 \/ kd mod 10 = 7 \/ kd mod 10 = 8 \/ kd mod 10 = 9) by lia.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; rewrite H;
[rewrite J0 | rewrite J1 | rewrite J2 | rewrite J3 | rewrite J4 | rewrite J5 | rewrite J6 | rewrite J7 | rewrite J8 | ];
reflexivity.
Qed.

(* ======================================== the suffix ======================================== *)
Lemma w6_suffix_tl : forall rest b r', hs_suffix rest (b :: r') -> hs_suffix rest r'.
Proof.
intros rest b r' (j & Hj & E). exists (S j).
assert (Hl : length (skipn j rest) = S (length r')) by (rewrite <- E; reflexivity).
rewrite length_skipn in Hl. split; [lia|].
replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, <- E. reflexivity.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* __asan_memset at 0x521a8 (the head block's call): the kernel's contract of the intrinsic *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6_MEMSET.

(* the kept registers and cells of the pod loop, from C to D *)
Definition w6_Lk (cx : hs_scx rsegs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) : list (hd_loc * Z) :=
hs_Rc rsegs cx ++ hs_Kc rsegs cx sh np ++
[(LCell XR 0xd8, Z.of_nat (length ps)); (LCell XR 0xc0, hs_at_of sh ps);
 (LCell XR 0xc8, cnt); (LCell XR 0xa8, 1); (LCell XR 0xe8, hs_first ps)].

(* ======================================== a cut's geometry and context ======================================== *)
Lemma w6_geo_of : forall cx E ly2 S2 W2 regs2 mem2 md2,
hs_pre rsegs B cx (hi_shA headamp_himg_A) -> hs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
w6_geo (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (e_pp (x_e rsegs cx)) /\
e_F (x_e rsegs cx) = frame_addr ly2 4 (x_pos rsegs cx) /\
spZ (x_regs rsegs cx) = e_R (x_e rsegs cx).
Proof using LAWS.
intros cx E ly2 S2 W2 regs2 mem2 md2 HP HC.
destruct (hs_pre_geom rsegs B cx HP) as (Hsp & HRk & HR47 & _ & HF0 & HFapp & HF32 & Happ).
pose proof HP as HP'.
destruct HP' as (HJ0 & _ & _ & _ & _ & HS & _ & HRs & HRstk & Hown & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpp & _)).
cbn [hi_cid hi_rsz headamp_himg_A] in HRs, Hown.
destruct HC as (HJ & _ & _ & Hperm & _).
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct HJ0 as (_ & Hly0 & _).
assert (HFa : e_F (x_e rsegs cx) = frame_addr ly2 4 (x_pos rsegs cx)).
{ rewrite HF0. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & E2 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & E0 & _). rewrite E2, E0. reflexivity. }
assert (Hin : In (4, x_pos rsegs cx) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (Hpp2 : In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hpp]).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 4 (x_pos rsegs cx) HAR Hpp2 Hin) as Hdj.
rewrite <- HFa in Hdj.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR Hpp2) as (_ & Hp4 & Hp1 & _).
destruct Hstk as (_ & _ & Hac & Hlo & _).
destruct (w6h_bounds _ HF32 HFapp) as (B1 & B2 & B3 & B4 & B5 & _).
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hp1, Hdj by reflexivity.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 4) with 1024 in Hdj.
pose proof ASAN_CEIL_range as (HC1 & _). unfold ASAN_CEIL in HC1.
pose proof (Z.div_mod (e_F (x_e rsegs cx)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (e_F (x_e rsegs cx)) 8 ltac:(lia)) as D2.
split; [|split; [exact HFa | exact Hsp]].
unfold w6_geo. split; [unfold T_SEG_STK, ASTACK in *; lia|].
split; [exact HR47|]. split; [exact HRk|]. split; [exact HFapp|].
do 5 (split; [lia|]). split; [exact Hp4|]. split; [lia|]. split; [|exact Hdj].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr, SHADOW_OFF in *. unfold Layout.PP_SIZE in *.
lia.
Qed.

Lemma w6_ctx_of : forall cx ly2 S2 W2 regs2 mem2 md2,
hs_pre rsegs B cx (hi_shA headamp_himg_A) -> hs_core rsegs B MT cx (hs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
w6_ctx B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2
  (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (x_pos rsegs cx).
Proof using LAWS.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC.
destruct (w6_geo_of cx _ ly2 S2 W2 regs2 mem2 md2 HP HC) as (_ & HFa & _).
pose proof (hs_rom_now rsegs B MT img_segs_low cx ly2 S2 W2 regs2 mem2 md2 HP HC) as Hrom.
pose proof HP as HP'. destruct HP' as (_ & _ & _ & _ & _ & HS & HR32 & HRs & HRstk & Hown & _).
assert (HR16 : e_R (x_e rsegs cx) mod 16 = 0).
{ pose proof (Z.div_mod (e_R (x_e rsegs cx)) 32 ltac:(lia)) as D. rewrite HR32, Z.add_0_r in D. rewrite D.
  replace (32 * (e_R (x_e rsegs cx) / 32)) with ((2 * (e_R (x_e rsegs cx) / 32)) * 16) by ring. apply Z_mod_mult. }
cbn [hi_cid hi_rsz headamp_himg_A] in HRs, Hown.
destruct HC as (HJ & _).
unfold w6_ctx. split; [exact HJ|]. split; [exact HR16|]. split; [rewrite <- HS; exact HRs|].
split; [exact HRstk|]. split; [exact Hown|]. split; [exact HFa | exact Hrom].
Qed.

(* the journal-and-frame part of a cut, carried across a block *)
Lemma w6_core_step : forall cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (Wr : Z -> Prop),
hs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Wr a -> (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) \/ E a) ->
hs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof using MTL.
intros cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Wr HC HJ Hr Hf Hp Hio Hmo Hm Hsub.
unfold hs_core, hs_mid in *.
destruct HC as (_ & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2).
split; [exact HJ|].
split; [intros r Hr0; rewrite (Hr r Hr0); exact (Hr2 r Hr0)|].
split; [rewrite Hf; exact Hf2|].
split; [eapply Permutation_trans; [exact Hp | exact Hp2]|].
split; [eapply same_io_trans; [exact Hio2 | exact Hio]|].
split; [exact (mle_station MT (x_Sc rsegs cx) S2 S3 0 0 MTL Hmo2 Hmo)|].
intros a Ha Hs HE. rewrite <- (Hm2 a Ha Hs HE). apply Hm; [exact Ha|].
intros HW. destruct (Hsub a HW) as [X|X]; [exact (Hs X) | exact (HE X)].
Qed.

Lemma w6_pod_base_mv : forall cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hs_core rsegs B MT cx (hs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> hs_suffix rest r' ->
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr r' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & H1 & _ & H3) HC HS.
split; [exact HC|]. split; [exact H1|]. split; [exact HS | exact H3].
Qed.

(* ======================================== the input at the cursor after the head ======================================== *)
Lemma w6_in_kept : forall cx rest r (W2 : world rsegs) mem2 (W1 : world rsegs) mem1,
hs_pre rsegs B cx (hi_shA headamp_himg_A) -> hs_in rsegs cx rest -> hs_suffix rest r ->
w6_geo (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (e_pp (x_e rsegs cx)) ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_src (x_e rsegs cx)) (hd_zbytes rest) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e rsegs cx)) (e_left (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6_head_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) a ->
 aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W2) mem2 a) ->
w6_in W1 mem1 (e_R (x_e rsegs cx)) (hs_cur rsegs cx rest r) r.
Proof.
intros cx rest r W2 mem2 W1 mem1 HP HI (j & Hj & ->) HG Hg Hra Hm.
destruct HI as (Hleft & Hg0 & Hra0 & _ & Ham & Hsrc & Htop & Hx).
assert (Hfsh0 : hd_fsh rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) (e_F (x_e rsegs cx)) headamp_A_shA).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
assert (Hcur : hs_cur rsegs cx rest (skipn j rest) = e_src (x_e rsegs cx) + Z.of_nat j)
  by (unfold hs_cur; rewrite length_skipn; lia).
unfold w6_in. rewrite Hcur. rewrite length_skipn.
assert (Hn : forall x, e_src (x_e rsegs cx) <= x < e_src (x_e rsegs cx) + Z.of_nat (length rest) ->
  0 <= x < kHighMemEnd /\ ~ w6_head_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) x /\
  ~ (e_R (x_e rsegs cx) <= x < e_R (x_e rsegs cx) + 0x160) /\
  ~ (e_R (x_e rsegs cx) - T_SEG_STK <= x < e_R (x_e rsegs cx))).
{ intros x Hx'. rewrite <- Hleft in Hx'. destruct (Hx x Hx') as (D1 & D2 & _).
  split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
  split; [intros HW; destruct (w6_hw_E1 (x_e rsegs cx) x HW) as [X|X]; [exact (D1 X) | exact (D2 X)]|].
  split; [intros X; apply D2; apply w6_inw1; right; right; exact X | exact D1]. }
split; [|split; [|split; [lia|split; [lia|split]]]].
- assert (Hg1 : hm_bytes rsegs (w_H W2) mem2 (e_src (x_e rsegs cx) + Z.of_nat j) (skipn j rest)).
  { pose proof (proj1 (hm_bytes_app rsegs (w_H W2) mem2 (e_src (x_e rsegs cx)) (firstn j rest) (skipn j rest))) as Happ.
    rewrite firstn_skipn in Happ. destruct (Happ Hg) as [_ H2].
    rewrite length_firstn, Nat.min_l in H2 by lia. exact H2. }
  apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W1) mem1 _ _ Hg1).
  intros x Hx'. rewrite length_skipn in Hx'. destruct (Hn x ltac:(lia)) as (Hb & Hw & _).
  apply Hm; [unfold kHighMemEnd in Hb; lia | exact Hw].
- intros x Hx'. destruct (Hn x ltac:(lia)) as (Hb & _).
  pose proof (hm_ra_not_fsh rsegs _ _ _ _ (e_src (x_e rsegs cx)) (e_left (x_e rsegs cx)) Hra0 Hfsh0 hm_sh_P0_big x
    ltac:(lia)) as Hnf.
  change (Z.of_nat (length headamp_A_shA)) with 80 in Hnf.
  destruct (w6_hw_shin _ _ _ x HG Hb Hnf) as [Hb2 Hw2].
  rewrite (Hm _ Hb2 Hw2). apply Hra. lia.
- unfold amem_range in *. lia.
- intros a Ha. destruct (Hn a ltac:(lia)) as (_ & _ & D3 & D4). lia.
Qed.

(* ======================================== the location lists of D and D0E ======================================== *)
Lemma w6_at_D0E : forall cx sh np ps cnt es rest H mem regs,
hs_at rsegs H mem regs (x_e rsegs cx)
  ((w6_Lk cx sh np ps cnt ++ [(LCell XR 0x118, Z.of_nat (length (@nil byte)))]) ++
   [(LCell XR 0xf8, Z.of_nat (length es))]) ->
getr regs 25 = w64 (hs_cur rsegs cx rest []) ->
hs_at rsegs H mem regs (x_e rsegs cx)
  (hs_L_Dc rsegs cx sh np ps cnt es ++ [(LCell XR 0x118, 0); (LReg 25, hs_cur rsegs cx rest [])]).
Proof.
intros cx sh np ps cnt es rest H mem regs A R25.
pose proof A as A'. unfold hs_at in A' |- *. apply Forall_app. split.
- apply (w6_fsub _ _ _ A'). unfold w6_Lk. w6_unf.
  repeat (apply Forall_cons; [cbv beta; left; w6_mem|]). apply Forall_nil.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd hd_at].
  + exact (w6_at_get _ _ _ _ _ (LCell XR 0x118) _ A ltac:(unfold w6_Lk; w6_unf; w6_mem)).
  + rewrite (w6_regZ regs (25%bv : bv 5) 25 eq_refl). exact R25.
Qed.

Lemma w6_at_D : forall cx sh np ps cnt es rest (b : byte) r' H mem regs,
hs_at rsegs H mem regs (x_e rsegs cx)
  ((w6_Lk cx sh np ps cnt ++ [(LCell XR 0x118, Z.of_nat (length (b :: r')))]) ++
   [(LCell XR 0xf8, Z.of_nat (length es))]) ->
w6_kind_R (bv_unsigned b) (hs_cur rsegs cx rest (b :: r')) (Z.of_nat (length r')) regs ->
hs_at rsegs H mem regs (x_e rsegs cx) (hs_L_D rsegs cx sh np ps cnt es rest r' (bv_unsigned b)).
Proof.
intros cx sh np ps cnt es rest b r' H mem regs A (R14 & R24 & R25 & R17 & RK).
pose proof (hm_byte_range b) as Hb.
assert (Hcur : hs_cur rsegs cx rest r' = hs_cur rsegs cx rest (b :: r') + 1) by (unfold hs_cur; cbn [length]; lia).
pose proof A as A'. unfold hs_at in A' |- *. unfold hs_L_D. apply Forall_app. split; [|apply Forall_app; split].
- apply (w6_fsub _ _ _ A'). unfold w6_Lk. w6_unf.
  repeat (apply Forall_cons; [cbv beta; left; w6_mem|]). apply Forall_nil.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]];
  cbn [fst snd hd_at].
  + replace (Z.of_nat (length r') + 1) with (Z.of_nat (length (b :: r'))) by (cbn [length]; lia).
    exact (w6_at_get _ _ _ _ _ (LCell XR 0x118) _ A ltac:(unfold w6_Lk; w6_unf; w6_mem)).
  + rewrite (w6_regZ regs (14%bv : bv 5) 14 eq_refl), Hcur.
    replace (hs_cur rsegs cx rest (b :: r') + 1 - 1) with (hs_cur rsegs cx rest (b :: r')) by lia. exact R14.
  + rewrite (w6_regZ regs (24%bv : bv 5) 24 eq_refl), Hcur. exact R24.
  + rewrite (w6_regZ regs (25%bv : bv 5) 25 eq_refl). exact R25.
  + rewrite (w6_regZ regs (17%bv : bv 5) 17 eq_refl). exact R17.
- destruct (bv_unsigned b mod 10 =? 9).
  + destruct RK as (_ & _ & R12).
    apply Forall_cons; [|apply Forall_nil]; cbn [fst snd hd_at].
    rewrite (w6_regZ regs (12%bv : bv 5) 12 eq_refl). exact R12.
  + destruct RK as (R10 & _ & R12 & R20).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd hd_at].
    * rewrite (w6_regZ regs (12%bv : bv 5) 12 eq_refl). exact R12.
    * rewrite (w6_regZ regs (20%bv : bv 5) 20 eq_refl), R20. f_equal. unfold sext8.
      destruct (Z.ltb_spec (bv_unsigned b) 128) as [Hl|Hl]; cbv beta iota.
      -- rewrite (Z.div_small (bv_unsigned b) 128) by lia. lia.
      -- rewrite <- (Z.div_unique (bv_unsigned b) 128 1 (bv_unsigned b - 128)) by lia. lia.
    * rewrite (w6_regZ regs (10%bv : bv 5) 10 eq_refl). apply bv_eq. rewrite R10. unfold w64.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small; [reflexivity | lia].
Qed.

(* the side conditions of a carried list: registers by computation, cells by w6_hw_cell / w6_tw_cell / w6_R_cell *)
Ltac w6_sides_head HG :=
try unfold w6_Lk; w6_unf;
repeat (apply Forall_cons; [unfold w6_side; cbn [fst hd_xv];
  lazymatch goal with
  | |- w6_regok _ _ = true => vm_compute; reflexivity
  | |- forall _, _ => let ii := fresh "ii" in let Hii := fresh "Hii" in
      intros ii Hii; apply (w6_hw_cell _ _ _ _ ii HG); [reflexivity | exact Hii]
  end|]); apply Forall_nil.
Ltac w6_sides_tail HG :=
try unfold w6_Lk; w6_unf;
repeat (apply Forall_cons; [unfold w6_side; cbn [fst hd_xv];
  lazymatch goal with
  | |- w6_regok _ _ = true => vm_compute; reflexivity
  | |- forall _, _ => let ii := fresh "ii" in let Hii := fresh "Hii" in
      intros ii Hii; apply (w6_tw_cell _ _ _ _ ii HG); [reflexivity | exact Hii]
  end|]); apply Forall_nil.
Ltac w6_sides_all HG :=
try unfold w6_Lk; w6_unf;
repeat (apply Forall_cons; [unfold w6_side; cbn [fst hd_xv];
  lazymatch goal with
  | |- w6_regok _ _ = true => vm_compute; reflexivity
  | |- forall _, _ => let ii := fresh "ii" in let Hii := fresh "Hii" in
      intros ii Hii; split; [apply (w6_R_cell _ _ _ _ ii HG); [reflexivity | exact Hii] | tauto]
  end|]); apply Forall_nil.
(* a list whose elements all lie in a literal list *)
Ltac w6_subs := try unfold w6_Lk; w6_unf; repeat (apply Forall_cons; [cbv beta; left; w6_mem|]); apply Forall_nil.

(* ======================================== W6a, the dispatch ======================================== *)
Theorem w6_disp : hs_piece_W6a_disp_stmt rsegs B MT.
Proof using MTL LAWS AMEMSET.
intros cx POST rest i k Hst HD HD0E.
unfold hs_from_D in HD. unfold hs_from_D0E in HD0E. unfold hs_from_C.
intros lyC SC WC regsC memC mdC sh np ps cnt es r Hlp Hle HC.
destruct Hst as (HP & _ & _ & HIN).
destruct HC as (HB & HAT & HFSH & HPP).
pose proof HB as HB0.
destruct HB as (HCORE & _ & HSUF & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hesl & _).
destruct (w6_geo_of cx _ _ _ _ _ _ _ HP HCORE) as (HG & HFa & HspZ).
pose proof (w6_ctx_of cx _ _ _ _ _ _ HP HCORE) as HCTX.
pose proof (w6_pp_len sh ps es Hwf Hesw Hesl) as Hppl.
unfold hs_at_cx in HAT.
(* the registers and the cell the head reads, at C *)
assert (A9 : getr regsC 9 = w64 (e_R (x_e rsegs cx))) by (apply (w6_at_reg _ _ _ _ _ 9 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (A19 : getr regsC 19 = w64 (shadow_addr (e_F (x_e rsegs cx))))
  by (apply (w6_at_reg _ _ _ _ _ 19 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (A23 : getr regsC 23 = w64 SHADOW_OFF) by (apply (w6_at_reg _ _ _ _ _ 23 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (A25 : getr regsC 25 = w64 (hs_cur rsegs cx rest r))
  by (apply (w6_at_reg _ _ _ _ _ 25 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (A11 : getr regsC 11 = w64 (Z.of_nat (length es)))
  by (apply (w6_at_reg _ _ _ _ _ 11 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (Af0 : val_mem rsegs (mrestrict (w_H WC) memC) (e_R (x_e rsegs cx) + 0x110) 8 (e_F (x_e rsegs cx) + 0xf0))
  by (exact (w6_at_cell8 _ _ _ _ _ XR 0x110 _ HAT ltac:(w6_unf; w6_mem))).
assert (A234 : forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regsC (Z_to_bv 5 q) = getr (x_regs rsegs cx) (Z_to_bv 5 q))
  by (destruct HCORE as (_ & Hq & _); exact Hq).
assert (A2 : getr regsC 2 = w64 (e_R (x_e rsegs cx))).
{ rewrite <- (w6_regZ regsC (2%bv : bv 5) 2 eq_refl), (A234 2 ltac:(lia)), (w6_regZ _ (2%bv : bv 5) 2 eq_refl).
  destruct HP as (_ & _ & H2 & _). exact H2. }
assert (A3 : getr regsC 3 = w64 (as_gp B)).
{ rewrite <- (w6_regZ regsC (3%bv : bv 5) 3 eq_refl), (A234 3 ltac:(lia)), (w6_regZ _ (3%bv : bv 5) 3 eq_refl).
  destruct HP as (_ & _ & _ & H3 & _). exact H3. }
assert (A4 : getr regsC 4 = w64 (as_tp B)).
{ rewrite <- (w6_regZ regsC (4%bv : bv 5) 4 eq_refl), (A234 4 ltac:(lia)), (w6_regZ _ (4%bv : bv 5) 4 eq_refl).
  destruct HP as (_ & _ & _ & _ & H4 & _). exact H4. }
(* the input at C *)
destruct (hs_in_now rsegs B MT cx rest hs_P0 lyC SC WC regsC memC mdC HP HIN HCORE HFSH eq_refl) as (HgC & HraC & _).
(* ---------------- the head block ---------------- *)
pose proof (w6_head B MT MTL LAWS AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsC _ _ _ (Z.of_nat (length es)) hs_P0
  HCTX A2 A9 A19 A3 A4 A11 Af0 HFSH eq_refl) as HH.
eapply SRr_bind; [exact HH|]. clear HH.
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & _ & Hd8 & Hsh0 & He0).
assert (HCORE1 : hs_core rsegs B MT cx (hs_E1 rsegs cx) ly1 S1 W1 regs1 mem1 md1).
{ apply (w6_core_step cx _ lyC SC WC regsC memC mdC ly1 S1 W1 regs1 mem1 md1
    (w6_head_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx))) HCORE HJ1).
  - intros q Hq. apply (w6_reg_kept regsC regs1 w6_caller_saved q Hr1). destruct Hq as [->|[->| ->]]; vm_compute; reflexivity.
  - exact Hf1.
  - exact Hp1.
  - exact Hio1.
  - exact Hmo1.
  - exact Hm1.
  - intros a Ha. rewrite HspZ. destruct (w6_hw_E1 (x_e rsegs cx) a Ha) as [X|X]; [left; exact X | right; left; exact X]. }
(* the kept registers and cells, at the head's end *)
assert (HAT1a : hs_at rsegs (w_H W1) mem1 regs1 (x_e rsegs cx)
  (w6_Lk cx sh np ps cnt ++ [(LCell XR 0x118, Z.of_nat (length r))])).
{ apply (w6_atl_tr (w6_head_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx))) w6_caller_saved (w_H WC) memC _ _ regsC _ _ _ Hr1 Hm1).
  - w6_sides_head HG.
  - apply (w6_fsub _ _ _ HAT). unfold w6_Lk. w6_unf.
    repeat (apply Forall_cons; [cbv beta; left; w6_mem|]). apply Forall_nil. }
assert (HAT1 : hs_at rsegs (w_H W1) mem1 regs1 (x_e rsegs cx)
  ((w6_Lk cx sh np ps cnt ++ [(LCell XR 0x118, Z.of_nat (length r))]) ++ [(LCell XR 0xf8, Z.of_nat (length es))])).
{ unfold hs_at in *. apply Forall_app. split; [exact HAT1a|]. apply Forall_cons; [exact Hd8 | apply Forall_nil]. }
clear HAT1a.
assert (B9 : getr regs1 9 = w64 (e_R (x_e rsegs cx)))
  by (rewrite (w6_kept_bv regsC regs1 w6_caller_saved (9%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A9).
assert (B23 : getr regs1 23 = w64 SHADOW_OFF)
  by (rewrite (w6_kept_bv regsC regs1 w6_caller_saved (23%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A23).
assert (B25 : getr regs1 25 = w64 (hs_cur rsegs cx rest r))
  by (rewrite (w6_kept_bv regsC regs1 w6_caller_saved (25%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A25).
assert (Bf8 : val_mem rsegs (mrestrict (w_H W1) mem1) (e_R (x_e rsegs cx) + 0x118) 8 (Z.of_nat (length r)))
  by (exact (w6_at_cell8 _ _ _ _ _ XR 0x118 _ HAT1 ltac:(unfold w6_Lk; w6_unf; w6_mem))).
(* e's shadow and e, the block pp and the input, at the head's end *)
assert (HFSH1 : hd_fsh rsegs (w_H W1) mem1 (e_F (x_e rsegs cx)) hs_PJ).
{ replace hs_PJ with (hm_setn hs_P0 30 13 0) by (vm_compute; reflexivity).
  apply (hm_fsh_set rsegs (w_H WC) memC (w_H W1) mem1 _ hs_P0 30 13 0 HFSH).
  - intros ii Hii. change (Z.of_nat 30) with 30 in Hii. change (Z.of_nat (30 + 13)) with 43 in Hii.
    replace (shadow_addr (e_F (x_e rsegs cx)) + ii) with (shadow_addr (e_F (x_e rsegs cx)) + 0x1e + (ii - 30)) by lia.
    apply Hsh0. lia.
  - intros ii Hii Hn. change (Z.of_nat (length hs_P0)) with 80 in Hii.
    change (Z.of_nat 30) with 30 in Hn. change (Z.of_nat (30 + 13)) with 43 in Hn.
    destruct (w6_hw_fsh _ _ _ ii HG ltac:(lia) ltac:(lia)) as [Hb Hw]. exact (Hm1 _ Hb Hw). }
assert (HE1 : hm_bytes rsegs (w_H W1) mem1 (e_F (x_e rsegs cx) + 0xf0) (zeros 104)).
{ change (zeros 104) with (repeat (Z_to_bv 8 0) 104). apply (hm_memset_bytes rsegs (w_H W1) mem1 _ 0 104).
  intros ii Hii. exact (He0 ii Hii). }
assert (HPP1 : hs_pp_at rsegs cx W1 mem1 (pc_image (PbCut sh ps (Some es)))).
{ unfold hs_pp_at in *. apply (hm_bytes_kept rsegs (w_H WC) memC (w_H W1) mem1 _ _ HPP).
  intros x Hx. rewrite Hppl in Hx.
  destruct (w6_hw_pp _ _ _ (x - e_pp (x_e rsegs cx)) HG ltac:(lia)) as [Hb Hw].
  replace x with (e_pp (x_e rsegs cx) + (x - e_pp (x_e rsegs cx))) by lia. exact (Hm1 _ Hb Hw). }
pose proof (w6_in_kept cx rest r WC memC W1 mem1 HP HIN HSUF HG HgC HraC Hm1) as HIN1.
pose proof (w6_ctx_of cx ly1 S1 W1 regs1 mem1 md1 HP HCORE1) as HCTX1.
(* ---------------- the kind block ---------------- *)
pose proof (w6_kind B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs1 _ _ _ (hs_cur rsegs cx rest r) r
  HCTX1 B9 B23 B25 Bf8 HIN1) as HK.
eapply SRr_bind; [exact HK|]. clear HK.
intros W3 c3 Hw3 [(Hr0 & HPOST) | (b & r' & Hr & HPOST)].
- (* no input left: D0E *)
  subst r.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & _).
  assert (HCORE3 : hs_core rsegs B MT cx (hs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
  { apply (w6_core_step cx _ ly1 S1 W1 regs1 mem1 md1 ly3 S3 W3 regs3 mem3 md3 (fun _ => False) HCORE1 HJ3).
    - intros q Hq. apply (w6_reg_kept regs1 regs3 [10]%bv q Hr3). destruct Hq as [->|[->| ->]]; vm_compute; reflexivity.
    - exact Hf3.
    - exact Hp3.
    - exact Hio3.
    - exact Hmo3.
    - intros a _ _. exact (Hm3 a).
    - intros a []. }
  apply (HD0E ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es Hlp Hle).
  split; [exact (w6_pod_base_mv cx sh np ps cnt es rest [] [] [] _ _ _ _ _ _ _ _ _ _ _ _ HB0 HCORE3 HSUF)|].
  split.
  { unfold hs_at_cx. apply (w6_at_D0E cx sh np ps cnt es rest).
    - apply (w6_atl_tr (fun _ => False) [10]%bv (w_H W1) mem1 _ _ regs1 _ _ _ Hr3 (fun a _ _ => Hm3 a)); [|exact HAT1].
      w6_sides_all HG.
    - rewrite (w6_kept_bv regs1 regs3 [10]%bv (25%bv : bv 5) Hr3 ltac:(vm_compute; reflexivity)). exact B25. }
  split; [exact (hm_fsh_kept rsegs _ _ _ _ _ _ HFSH1 (fun ii _ => Hm3 _))|].
  split; [exact (hm_bytes_kept rsegs _ _ _ _ _ _ HPP1 (fun x _ => Hm3 x))|].
  exact (hm_bytes_kept rsegs _ _ _ _ _ _ HE1 (fun x _ => Hm3 x)).
- (* the kind byte b: the entry of kind % 10 *)
  subst r.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & HR3).
  assert (Hr3' : forall q : bv 5, bv_unsigned q <> 0 -> ~ In q [10; 11; 12; 14; 17; 20; 24; 25]%bv ->
    getr regs3 q = getr regs1 q).
  { intros q Hq0 Hqn. apply Hr3; [exact Hq0|]. unfold w6_kind_clob. destruct (_ =? 9); [|exact Hqn].
    intros Hin. apply Hqn. cbn [In] in Hin |- *. tauto. }
  assert (HCORE3 : hs_core rsegs B MT cx (hs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
  { apply (w6_core_step cx _ ly1 S1 W1 regs1 mem1 md1 ly3 S3 W3 regs3 mem3 md3 (fun _ => False) HCORE1 HJ3).
    - intros q Hq. apply (w6_reg_kept regs1 regs3 [10; 11; 12; 14; 17; 20; 24; 25]%bv q Hr3').
      destruct Hq as [->|[->| ->]]; vm_compute; reflexivity.
    - exact Hf3.
    - exact Hp3.
    - exact Hio3.
    - exact Hmo3.
    - intros a _ _. exact (Hm3 a).
    - intros a []. }
  rewrite (w6_case_pc_D (bv_unsigned b)).
  apply (HD (bv_unsigned b) ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es (b :: r') r' Hlp Hle).
  pose proof (w6_suffix_tl rest b r' HSUF) as HSUF'.
  split; [exact (w6_pod_base_mv cx sh np ps cnt es rest (b :: r') (b :: r') r' _ _ _ _ _ _ _ _ _ _ _ _ HB0 HCORE3 HSUF')|].
  split.
  { unfold hs_at_cx. apply (w6_at_D cx sh np ps cnt es rest b r').
    - apply (w6_atl_tr (fun _ => False) [10; 11; 12; 14; 17; 20; 24; 25]%bv (w_H W1) mem1 _ _ regs1 _ _ _ Hr3'
        (fun a _ _ => Hm3 a)); [|exact HAT1].
      w6_sides_all HG.
    - exact HR3. }
  split; [exact (hm_fsh_kept rsegs _ _ _ _ _ _ HFSH1 (fun ii _ => Hm3 _))|].
  split; [exact (hm_bytes_kept rsegs _ _ _ _ _ _ HPP1 (fun x _ => Hm3 x))|].
  split; [exact (hm_bytes_kept rsegs _ _ _ _ _ _ HE1 (fun x _ => Hm3 x))|].
  split; [exact HSUF|].
  split; [reflexivity|].
  split; [exact (hm_byte_range b)|].
  discriminate.
Qed.

(* ======================================== W6a, the cases 2 and 3 ======================================== *)
(* a block that writes no byte: the cut's journal-and-frame part and a carried location list *)
Lemma w6_blk_step : forall cx clob L lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB,
hs_core rsegs B MT cx (hs_E1 rsegs cx) lyA SA WA regsA memA mdA ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) lyB SB WB memB mdB (x_k rsegs cx) ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regsB r = getr regsA r) ->
frames SB = frames SA -> Permutation (ablocks B lyB SB) (ablocks B lyA SA) -> same_io mdA mdB -> mo_le MT SA SB 0 ->
(forall a, aview rsegs (w_H WB) memB a = aview rsegs (w_H WA) memA a) ->
w6_regok clob 2 = true -> w6_regok clob 3 = true -> w6_regok clob 4 = true ->
Forall (w6_side clob (fun _ => False) (x_e rsegs cx)) L ->
hs_at rsegs (w_H WA) memA regsA (x_e rsegs cx) L ->
hs_core rsegs B MT cx (hs_E1 rsegs cx) lyB SB WB regsB memB mdB /\ hs_at rsegs (w_H WB) memB regsB (x_e rsegs cx) L.
Proof using MTL.
intros cx clob L lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB HC HJ Hr Hf Hp Hio Hmo Hm R2 R3 R4 Hs A.
split.
- apply (w6_core_step cx _ lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB (fun _ => False) HC HJ).
  + intros q Hq. apply (w6_reg_kept regsA regsB clob q Hr). destruct Hq as [->|[->| ->]]; assumption.
  + exact Hf.
  + exact Hp.
  + exact Hio.
  + exact Hmo.
  + intros a _ _. exact (Hm a).
  + intros a [].
- exact (w6_atl_tr (fun _ => False) clob (w_H WA) memA (w_H WB) memB regsA regsB _ L Hr (fun a _ _ => Hm a) Hs A).
Qed.

(* the tail block from 0x82308 / 0x8235c and the cut J it ends at *)
Lemma w6_tail_J : forall (c3 : bool) cx POST rest i k sh np ps cnt es rr rD lyD SD WD regsD memD mdD
  lyT ST WT regsT memT mdT rJ vm v,
hs_pre rsegs B cx (hi_shA headamp_himg_A) -> hs_from_J rsegs B MT cx POST rest i k -> (length ps = i)%nat -> (length es = k)%nat ->
hs_pod_base rsegs B MT cx sh np ps cnt es rest rr rD lyD SD WD regsD memD mdD ->
hs_core rsegs B MT cx (hs_E1 rsegs cx) lyT ST WT regsT memT mdT ->
hs_at rsegs (w_H WT) memT regsT (x_e rsegs cx) (hs_L_Dc rsegs cx sh np ps cnt es) ->
getr regsT 20 = w64 (shadow_addr (e_pp (x_e rsegs cx) + 0x4000)) ->
getr regsT 11 = w64 (Z.of_nat (length rJ)) -> getr regsT 12 = w64 v -> getr regsT 24 = w64 (hs_cur rsegs cx rest rJ) ->
v mod 2 ^ 32 = vm mod 2 ^ 32 ->
(Ent (if c3 then POD_FLOAT else POD_INT) 4 (le32 vm), rJ) = ent_build rr ->
hs_suffix rest rJ ->
hm_bytes rsegs (w_H WT) memT (e_F (x_e rsegs cx) + 0xf0) (zeros 104) ->
hs_fsh_at rsegs cx WT memT hs_PJ ->
hs_pp_at rsegs cx WT memT (pc_image (PbCut sh ps (Some es))) ->
SRr rsegs WT (cfg_at rsegs (if c3 then W6_T3 else W6_T2) regsT memT mdT) POST.
Proof using MTL LAWS.
intros c3 cx POST rest i k sh np ps cnt es rr rD lyD SD WD regsD memD mdD lyT ST WT regsT memT mdT rJ vm v
  HP HJ Hlp Hle HB HCT HAT T20 T11 T12 T24 Hv Hed HsJ HZ HFSH HPP.
pose proof HB as HB0.
destruct HB as (_ & _ & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hesl & _).
destruct (w6_geo_of cx _ _ _ _ _ _ _ HP HCT) as (HG & HFa & HspZ).
pose proof (w6_ctx_of cx _ _ _ _ _ _ HP HCT) as HCTX.
pose proof (w6_pp_len sh ps es Hwf Hesw Hesl) as Hppl.
assert (T9 : getr regsT 9 = w64 (e_R (x_e rsegs cx)))
  by (apply (w6_at_reg _ _ _ _ _ 9 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (Tf0 : val_mem rsegs (mrestrict (w_H WT) memT) (e_R (x_e rsegs cx) + 0x110) 8 (e_F (x_e rsegs cx) + 0xf0))
  by (exact (w6_at_cell8 _ _ _ _ _ XR 0x110 _ HAT ltac:(w6_unf; w6_mem))).
pose proof (w6_tail_all B MT MTL LAWS c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsT _ _ _ (Z.of_nat (length rJ)) v
  (hs_cur rsegs cx rest rJ) HCTX T9 Tf0 T11 T12 T24) as HTT.
eapply SRr_bind; [exact HTT|]. clear HTT.
intros WJ cJ HwJ (lyJ & SJ & regsJ & memJ & mdJ & -> & HJJ & HrJ & HfJ & HpJ & HioJ & HmoJ & HmJ &
  (J10 & J13 & J25 & Vt & Vs & Vv & Vn)).
assert (HCJ : hs_core rsegs B MT cx (hs_E1 rsegs cx) lyJ SJ WJ regsJ memJ mdJ).
{ apply (w6_core_step cx _ lyT ST WT regsT memT mdT lyJ SJ WJ regsJ memJ mdJ
    (w6_tail_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx))) HCT HJJ).
  - intros q Hq. apply (w6_reg_kept regsT regsJ [10; 13; 25]%bv q HrJ). destruct Hq as [->|[->| ->]]; vm_compute; reflexivity.
  - exact HfJ.
  - exact HpJ.
  - exact HioJ.
  - exact HmoJ.
  - exact HmJ.
  - intros a Ha. right. left. exact (w6_tw_E1 (x_e rsegs cx) a Ha). }
unfold hs_from_J in HJ.
apply (HJ lyJ SJ WJ regsJ memJ mdJ sh np ps cnt es rr rJ (Ent (if c3 then POD_FLOAT else POD_INT) 4 (le32 vm)) Hlp Hle).
split; [exact (w6_pod_base_mv cx sh np ps cnt es rest rr rD rJ _ _ _ _ _ _ _ _ _ _ _ _ HB0 HCJ HsJ)|].
split.
{ assert (HATJ : hs_at rsegs (w_H WJ) memJ regsJ (x_e rsegs cx) (hs_L_Dc rsegs cx sh np ps cnt es)).
  { apply (w6_atl_tr (w6_tail_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx))) [10; 13; 25]%bv (w_H WT) memT _ _ regsT _ _ _
      HrJ HmJ); [|exact HAT].
    w6_sides_tail HG. }
  unfold hs_at_cx. pose proof HATJ as HATJ'. unfold hs_at in HATJ' |- *.
  apply Forall_app. split; [|apply Forall_app; split].
  - apply (w6_fsub _ _ _ HATJ'). w6_subs.
  - exact HATJ'.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd hd_at hd_xv].
    + rewrite (w6_regZ regsJ (20%bv : bv 5) 20 eq_refl).
      rewrite (w6_kept_bv regsT regsJ [10; 13; 25]%bv (20%bv : bv 5) HrJ ltac:(vm_compute; reflexivity)). exact T20.
    + rewrite (w6_regZ regsJ (25%bv : bv 5) 25 eq_refl). exact J25.
    + exact Vn. }
split.
{ unfold hs_fsh_at in *. apply (hm_fsh_kept rsegs (w_H WT) memT (w_H WJ) memJ _ _ HFSH).
  intros ii Hii. change (Z.of_nat (length hs_PJ)) with 80 in Hii.
  destruct (w6_tw_fsh _ _ _ ii HG Hii) as [Hb Hw]. exact (HmJ _ Hb Hw). }
split.
{ unfold hs_pp_at in *. apply (hm_bytes_kept rsegs (w_H WT) memT (w_H WJ) memJ _ _ HPP).
  intros x Hx. rewrite Hppl in Hx.
  destruct (w6_tw_pp _ _ _ (x - e_pp (x_e rsegs cx)) HG ltac:(lia)) as [Hb Hw].
  replace x with (e_pp (x_e rsegs cx) + (x - e_pp (x_e rsegs cx))) by lia. exact (HmJ _ Hb Hw). }
split.
{ (* e: the type, the size 4, the value's four bytes, 92 zeros *)
  assert (HEJ : hm_bytes rsegs (w_H WJ) memJ (e_F (x_e rsegs cx) + 0xf0)
    (ent_mem (Ent (if c3 then POD_FLOAT else POD_INT) 4 (le32 vm)))).
  { unfold ent_mem. cbn [e_type e_size e_body].
    replace (96 - length (le32 vm))%nat with 92%nat by (unfold le32; rewrite length_Z_to_le_bytes; reflexivity).
    apply hm_bytes_app. split.
    { unfold le32. apply hm_bytes_of_val. exact Vt. }
    replace (Z.of_nat (length (le32 (if c3 then POD_FLOAT else POD_INT)))) with 4
      by (unfold le32; rewrite length_Z_to_le_bytes; reflexivity).
    apply hm_bytes_app. split.
    { replace (e_F (x_e rsegs cx) + 0xf0 + 4) with (e_F (x_e rsegs cx) + 0xf4) by lia.
      unfold le32. apply hm_bytes_of_val. exact Vs. }
    replace (Z.of_nat (length (le32 4))) with 4 by (unfold le32; rewrite length_Z_to_le_bytes; reflexivity).
    apply hm_bytes_app. split.
    { replace (e_F (x_e rsegs cx) + 0xf0 + 4 + 4) with (e_F (x_e rsegs cx) + 0xf8) by lia.
      unfold le32. apply hm_bytes_of_val. apply (proj1 (w6_val_mod32 _ _ vm)). rewrite <- Hv. exact Vv. }
    replace (Z.of_nat (length (le32 vm))) with 4 by (unfold le32; rewrite length_Z_to_le_bytes; reflexivity).
    pose proof (hm_bytes_slice rsegs _ _ _ (zeros 104) 12 92 HZ ltac:(unfold zeros; rewrite repeat_length; lia)) as HZ1.
    change (hm_slice (zeros 104) 12 92) with (zeros 92) in HZ1.
    replace (e_F (x_e rsegs cx) + 0xf0 + 4 + 4 + 4) with (e_F (x_e rsegs cx) + 0xf0 + Z.of_nat 12) by lia.
    apply (hm_bytes_kept rsegs (w_H WT) memT (w_H WJ) memJ _ _ HZ1).
    intros x Hx. change (Z.of_nat (length (zeros 92))) with 92 in Hx.
    destruct (w6_tw_e _ _ _ (x - (e_F (x_e rsegs cx) + 0xf0)) HG ltac:(lia)) as [Hb Hw].
    replace x with (e_F (x_e rsegs cx) + 0xf0 + (x - (e_F (x_e rsegs cx) + 0xf0))) by lia. exact (HmJ _ Hb Hw). }
  exact HEJ. }
split; [exact Hed|].
pose proof (ent_build_wf rr) as X. rewrite <- Hed in X. exact X.
Qed.

(* one of the two cases, from its entry D to J *)
Lemma w6_case_gen : forall c3 : bool,
w6_case_head_stmt B MT c3 -> hd_u32_stmt B MT (if c3 then W6_U3 else W6_U2) (if c3 then W6_T3 else W6_T2) ->
forall cx POST rest i k kd, kd mod 10 = (if c3 then 3 else 2) ->
hs_start_M01 rsegs B cx rest -> hs_from_J rsegs B MT cx POST rest i k -> hs_from_D rsegs B MT cx POST rest i k kd.
Proof using MTL LAWS.
intros c3 HH HU cx POST rest i k kd Hkd Hst HJ.
unfold hs_from_D.
intros lyD SD WD regsD memD mdD sh np ps cnt es rr r Hlp Hle HD.
destruct Hst as (HP & _ & _ & HIN).
destruct HD as (HB & HAT & HFSH & HPP & HE & Hsrr & Hfu & Hkd256 & Hrr).
pose proof HB as HB0.
destruct HB as (HCORE & _ & HSUF & _).
destruct (w6_geo_of cx _ _ _ _ _ _ _ HP HCORE) as (HG & HFa & HspZ).
pose proof (w6_ctx_of cx _ _ _ _ _ _ HP HCORE) as HCTX.
unfold hs_at_cx in HAT. unfold hs_fsh_at in HFSH.
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd. subst r0.
rewrite (w6_rs_pc_23 c3 (bv_unsigned b) Hkd).
(* the registers and cells at D *)
assert (D9 : getr regsD 9 = w64 (e_R (x_e rsegs cx)))
  by (apply (w6_at_reg _ _ _ _ _ 9 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (D23 : getr regsD 23 = w64 SHADOW_OFF) by (apply (w6_at_reg _ _ _ _ _ 23 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (D24 : getr regsD 24 = w64 (hs_cur rsegs cx rest r))
  by (apply (w6_at_reg _ _ _ _ _ 24 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (D25 : getr regsD 25 = w64 (Z.of_nat (length r)))
  by (apply (w6_at_reg _ _ _ _ _ 25 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (D14 : getr regsD 14 = w64 (hs_cur rsegs cx rest r - 1))
  by (apply (w6_at_reg _ _ _ _ _ 14 _ _ HAT); [w6_unf; w6_mem | reflexivity]).
assert (Df8 : val_mem rsegs (mrestrict (w_H WD) memD) (e_R (x_e rsegs cx) + 0x118) 8 (Z.of_nat (length r) + 1))
  by (exact (w6_at_cell8 _ _ _ _ _ XR 0x118 _ HAT ltac:(w6_unf; w6_mem))).
assert (Db0 : val_mem rsegs (mrestrict (w_H WD) memD) (e_R (x_e rsegs cx) + 0xd0) 8 (shadow_addr (e_pp (x_e rsegs cx) + 0x4000)))
  by (exact (w6_at_cell8 _ _ _ _ _ XR 0xd0 _ HAT ltac:(w6_unf; w6_mem))).
(* the list the head block carries *)
assert (HATc : hs_at rsegs (w_H WD) memD regsD (x_e rsegs cx)
  (hs_L_Dc rsegs cx sh np ps cnt es ++ [(LCell XR 0x118, Z.of_nat (length r) + 1); (LReg 14, hs_cur rsegs cx rest r - 1)])).
{ pose proof HAT as HAT'. unfold hs_at in HAT' |- *. apply (w6_fsub _ _ _ HAT'). w6_subs. }
(* the input at the cursor, at D *)
destruct (hs_in_now rsegs B MT cx rest hs_PJ lyD SD WD regsD memD mdD HP HIN HCORE HFSH eq_refl) as (HgD & HraD & _).
pose proof (w6_in_kept cx rest r WD memD WD memD HP HIN HSUF HG HgD HraD (fun a _ _ => eq_refl)) as HIND.
assert (HHIN : w6_head_in WD memD regsD (e_R (x_e rsegs cx)) (hs_cur rsegs cx rest r)
  (shadow_addr (e_pp (x_e rsegs cx) + 0x4000)) r).
{ refine (conj D9 (conj D23 (conj D24 (conj D25 (conj D14 (conj Df8 (conj Db0 (conj (w6_vb_range _ _ _ HG)
    (conj (w6_cur_pos cx rest b r HIN Hsrr) HIND))))))))). }
(* the table's shadow, at D *)
assert (HRT : range_addressable (aview rsegs (w_H WD) memD) SHADOW_OFF (if c3 then W6_FLOATS else W6_INTS)
  (if c3 then 84 else 56)).
{ assert (Hg0 : range_addressable (aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx)) SHADOW_OFF
    (if c3 then W6_FLOATS else W6_INTS) (if c3 then 84 else 56)).
  { pose proof HP as HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgl & _).
    change (hi_globs headamp_himg_A) with headamp_A_globs in Hgl. rewrite Forall_forall in Hgl.
    destruct c3.
    - exact (Hgl (0x21060, 84) ltac:(unfold headamp_A_globs; w6_mem)).
    - exact (Hgl (0x21000, 56) ltac:(unfold headamp_A_globs; w6_mem)). }
  intros x Hx.
  rewrite (hs_core_kept rsegs B MT cx _ _ _ _ _ _ HP HCORE (shadow_of_addr SHADOW_OFF x)); [exact (Hg0 x Hx)|].
  apply (hs_wr_shadow rsegs B cx x HP).
  - destruct c3; cbv beta iota in Hx; unfold kHighMemEnd, W6_FLOATS, W6_INTS in *; lia.
  - intros y Hy. apply Hg0. lia. }
(* ---------------- the case's head block ---------------- *)
pose proof (HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsD _ _ _ (hs_cur rsegs cx rest r)
  (shadow_addr (e_pp (x_e rsegs cx) + 0x4000)) r HCTX HHIN HRT) as HH1.
eapply SRr_bind; [exact HH1|]. clear HH1.
intros WH cH HwH HPOST. cbv beta zeta in HPOST.
revert HPOST. destruct (Z.odd (fst (Cursor.fuzz_u8 r))) eqn:Eodd; intros HPOST.
- (* m odd: the fuzz_u32 block, then the tail *)
  destruct r as [|b' r1]; [cbn in Eodd; discriminate Eodd|].
  cbn [Cursor.fuzz_u8 fst snd] in HPOST, Eodd.
  destruct HPOST as (lyH & SH & regsH & memH & mdH & -> & HJH & HrH & HfH & HpH & HioH & HmoH & HmH &
    (H11 & H12 & H24 & H20)).
  destruct (w6_blk_step cx [10; 11; 12; 13; 20; 24]%bv
    (hs_L_Dc rsegs cx sh np ps cnt es ++
     [(LCell XR 0x118, Z.of_nat (length (b' :: r1)) + 1); (LReg 14, hs_cur rsegs cx rest (b' :: r1) - 1)])
    lyD SD WD regsD memD mdD lyH SH WH regsH memH mdH HCORE HJH HrH
    HfH HpH HioH HmoH HmH eq_refl eq_refl eq_refl ltac:(w6_sides_all HG) HATc) as [HCH HATH].
  assert (H9 : getr regsH 9 = w64 (e_R (x_e rsegs cx)))
    by (apply (w6_at_reg _ _ _ _ _ 9 _ _ HATH); [w6_unf; w6_mem | reflexivity]).
  assert (H23 : getr regsH 23 = w64 SHADOW_OFF)
    by (apply (w6_at_reg _ _ _ _ _ 23 _ _ HATH); [w6_unf; w6_mem | reflexivity]).
  assert (H14 : getr regsH 14 = w64 (hs_cur rsegs cx rest (b' :: r1) + 1 - 2)).
  { replace (hs_cur rsegs cx rest (b' :: r1) + 1 - 2) with (hs_cur rsegs cx rest (b' :: r1) - 1) by lia.
    apply (w6_at_reg _ _ _ _ _ 14 _ _ HATH); [w6_unf; w6_mem | reflexivity]. }
  assert (Hf8 : val_mem rsegs (mrestrict (w_H WH) memH) (e_R (x_e rsegs cx) + 280) 8 (Z.of_nat (length r1) + 2)).
  { replace (Z.of_nat (length r1) + 2) with (Z.of_nat (length (b' :: r1)) + 1) by (cbn [length]; lia).
    exact (w6_at_cell8 _ _ _ _ _ XR 0x118 _ HATH ltac:(w6_unf; w6_mem)). }
  destruct HIND as (HgI & HraI & HcI & HtI & HamI & HexI).
  cbn [length] in HraI, HtI, HamI, HexI. rewrite Nat2Z.inj_succ in HraI, HtI, HamI, HexI.
  assert (HgH : garr8 rsegs (mrestrict (w_H WH) memH) (hs_cur rsegs cx rest (b' :: r1) + 1) (u8s r1)).
  { pose proof (proj1 (hm_bytes_app rsegs (w_H WD) memD (hs_cur rsegs cx rest (b' :: r1)) [b'] r1) HgI) as [_ X].
    change (Z.of_nat (length [b'])) with 1 in X.
    exact (hm_bytes_kept rsegs _ _ _ _ _ _ X (fun x _ => HmH x)). }
  assert (HraH : range_addressable (aview rsegs (w_H WH) memH) SHADOW_OFF (hs_cur rsegs cx rest (b' :: r1) + 1)
    (Z.of_nat (length r1))).
  { intros x Hx. rewrite HmH. apply HraI. lia. }
  pose proof (HU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsH (e_R (x_e rsegs cx)) (hs_cur rsegs cx rest (b' :: r1) + 1)
    (Z.of_nat (length r1)) (Z.of_nat (length r1) + 2) r1 eq_refl eq_refl HJH H9 H11 H14 H23 H24 Hf8) as HU1.
  pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  pose proof (HU1 ltac:(unfold T_SEG_STK, ASTACK in *; lia) ltac:(unfold T_SEG_STK, ASTACK in *; lia)
    ltac:(pose proof (w6_cur_pos cx rest b (b' :: r1) HIN Hsrr); lia)
    ltac:(unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia)
    ltac:(intros a Ha; pose proof (HexI a ltac:(lia)); unfold T_SEG_STK, ASTACK in *; lia) HgH HraH) as HU2'. clear HU1.
  eapply SRr_bind; [exact HU2'|]. clear HU2'.
  intros WU cU HwU (lyU & SU & regsU & memU & mdU & -> & HJU & HrU & HfU & HpU & HioU & HmoU & HmU &
    (U12 & U11 & U24 & U23)).
  destruct (w6_blk_step cx [11; 12; 13; 14; 15; 16; 24]%bv (hs_L_Dc rsegs cx sh np ps cnt es) lyH SH WH regsH memH mdH
    lyU SU WU regsU memU mdU HCH HJU HrU HfU HpU HioU HmoU HmU eq_refl eq_refl eq_refl ltac:(w6_sides_all HG)
    ltac:(unfold hs_at in HATH |- *; apply Forall_app in HATH as [X _]; exact X)) as [HCU HATU].
  apply (w6_tail_J c3 cx POST rest i k sh np ps cnt es (b :: b' :: r1) (b' :: r1) lyD SD WD regsD memD mdD
    lyU SU WU regsU memU mdU (snd (Cursor.fuzz_u32 r1)) (fst (Cursor.fuzz_u32 r1)) (fst (Cursor.fuzz_u32 r1))
    HP HJ Hlp Hle HB0 HCU HATU).
  + rewrite (w6_kept_bv regsH regsU [11; 12; 13; 14; 15; 16; 24]%bv (20%bv : bv 5) HrU ltac:(vm_compute; reflexivity)).
    exact H20.
  + rewrite fuzz_u32_rest_len. exact U11.
  + exact U12.
  + rewrite Cursor.fuzz_u32_rest, w6_cur_skip.
    replace (hs_cur rsegs cx rest r1) with (hs_cur rsegs cx rest (b' :: r1) + 1) by (unfold hs_cur; cbn [length]; lia).
    exact U24.
  + reflexivity.
  + rewrite (w6_ent_build c3 b (b' :: r1) Hkd). cbn [Cursor.fuzz_u8 fst snd]. rewrite Eodd. reflexivity.
  + rewrite Cursor.fuzz_u32_rest. apply w6_suffix_skip. exact (w6_suffix_tl rest b' r1 HSUF).
  + apply (hm_bytes_kept rsegs _ _ _ _ _ _ HE). intros x _. rewrite HmU. exact (HmH x).
  + unfold hs_fsh_at. apply (hm_fsh_kept rsegs _ _ _ _ _ _ HFSH). intros ii _. rewrite HmU. exact (HmH _).
  + unfold hs_pp_at in *. apply (hm_bytes_kept rsegs _ _ _ _ _ _ HPP). intros x _. rewrite HmU. exact (HmH x).
- (* m even (or no byte): the tail *)
  destruct HPOST as (lyH & SH & regsH & memH & mdH & -> & HJH & HrH & HfH & HpH & HioH & HmoH & HmH &
    ((v & H12 & Hv) & H11 & H24 & H20)).
  destruct (w6_blk_step cx [10; 11; 12; 13; 20; 24]%bv (hs_L_Dc rsegs cx sh np ps cnt es) lyD SD WD regsD memD mdD
    lyH SH WH regsH memH mdH HCORE HJH HrH HfH HpH HioH HmoH HmH eq_refl eq_refl eq_refl ltac:(w6_sides_all HG)
    ltac:(unfold hs_at in HATc |- *; apply Forall_app in HATc as [X _]; exact X)) as [HCH HATH].
  apply (w6_tail_J c3 cx POST rest i k sh np ps cnt es (b :: r) r lyD SD WD regsD memD mdD
    lyH SH WH regsH memH mdH (snd (Cursor.fuzz_u8 r))
    (if c3 then w6_float_even (fst (Cursor.fuzz_u8 r)) else w6_int_even (fst (Cursor.fuzz_u8 r))) v
    HP HJ Hlp Hle HB0 HCH HATH).
  + exact H20.
  + exact H11.
  + exact H12.
  + rewrite H24. f_equal. rewrite Cursor.fuzz_u8_spec. cbn [snd]. rewrite w6_cur_skip, length_skipn. lia.
  + exact Hv.
  + rewrite (w6_ent_build c3 b r Hkd), Eodd. reflexivity.
  + rewrite Cursor.fuzz_u8_spec. cbn [snd]. apply w6_suffix_skip. exact HSUF.
  + exact (hm_bytes_kept rsegs _ _ _ _ _ _ HE (fun x _ => HmH x)).
  + exact (hm_fsh_kept rsegs _ _ _ _ _ _ HFSH (fun ii _ => HmH _)).
  + exact (hm_bytes_kept rsegs _ _ _ _ _ _ HPP (fun x _ => HmH x)).
Qed.

Theorem w6_cases : hs_piece_W6a_cases_stmt rsegs B MT.
Proof using MTL LAWS.
intros cx POST rest i k kd Hst Hin HJ.
cbn [In] in Hin. destruct Hin as [H2|[H3|[]]].
- exact (w6_case_gen false (w6_c2h B MT MTL LAWS) (hd_u32_block2 B MT MTL LAWS) cx POST rest i k kd (eq_sym H2) Hst HJ).
- exact (w6_case_gen true (w6_c3h B MT MTL LAWS) (hd_u32_block3 B MT MTL LAWS) cx POST rest i k kd (eq_sym H3) Hst HJ).
Qed.

End d.
End b.

Check w6_disp.
Check w6_cases.
Print Assumptions w6_disp.
Print Assumptions w6_cases.
