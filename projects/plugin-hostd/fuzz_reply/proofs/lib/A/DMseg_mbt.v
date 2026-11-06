(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMseg_mbt.v (commit fe876300d09, Quarantine::Drain walk set; file sha256 d49000e1b7f1) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 9 image addresses moved by code-verified function pairs (8 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 1 code pcs the tool read as sizes, by funcpair.py), and 18 pcs named in comments; no other numeral changed. *)
(* MergeBatches (0x33b74), the tail of a merge step, 0x33bf8 -> 0x33bac (or the return to 0x33a38).

   On entry the successor's slots are already copied (DMseg_mbc.v) and: a4 = [cur], t0 = [nx], a3 = size(cur) [csz],
   t1 = the merged count [ncn], a2 = the bytes extracted so far [tot], a0 = the global list (A_QUAR + 160), a1 = the
   temp list (Recycle's sp = MergeBatches' sp + 16), a6 = -8192, a7 = 8192.  The code:
   - 0x33bf8-0x33c14: size(cur) := csz + size(nx) - 8192, count(cur) := ncn, size(nx) := 8192, count(nx) := 0;
     0x33c18 beqz (list count) -> 0x33cdc, the CHECK(!empty()) die path (decided by the fact list count >= 1);
   - 0x33c1c-0x33c28: next(cur) := next(nx); beq (list last = nx) -> 0x33c50: list last := cur;
   - list count -= 1; next(nx) := 0; push nx on the temp list (empty: first := nx, count := 1; else
     next(temp last) := nx, count += 1); temp last := nx; temp bytes += 8192; a2 += 8192 (0x33c2c-0x33c84);
   - 0x33c88 t0 := next(cur); bnez -> 0x33bac [at_TCONT], else 0x33c90: list bytes -= a2, ret to 0x33a38 [at_TEXIT]. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kSpaceSize, TFIB_IMG_END,
kBatchBytes, kBatchSlots, TFIB_TP, A_QUAR, A_ALLOCATOR, o_quar in *.
Lemma zcanon_negadd_r : forall a b, 0 <= b <= a -> a < M64 -> zcanon (a + zcanon (b * zcanon (-1))) = a - b.
Proof. intros a b H H2. rewrite Z.add_comm. exact (zcanon_negadd a b H H2). Qed.
(* a6 = lui 0xffffe = 2^64 - 8192 *)
Definition M8192 : Z := 18446744073709543424.
Lemma zcanon_add_m8192 : forall a, 8192 <= a < M64 -> zcanon (a + 18446744073709543424) = a - 8192.
Proof.
intros a H. unfold zcanon. replace (a + 18446744073709543424) with ((a - 8192) + 1 * M64) by (unfold M64 in *; lia).
rewrite Z_mod_plus_full. apply Z.mod_small. unfold M64 in *; lia.
Qed.
(* `sub a1, a1, a2` with a2 = tot + 8192 built as (-tot) + (-8192) *)
Lemma zcanon_sub_8192 : forall a b, 0 <= b -> b + 8192 <= a -> a < M64 ->
zcanon (zcanon (zcanon (b * zcanon (-1)) + zcanon (-8192)) + a) = a - b - 8192.
Proof.
intros a b Hb Hba HM. unfold zcanon.
change ((-1) mod M64) with (M64 - 1). change ((-8192) mod M64) with (M64 - 8192).
rewrite (Zplus_mod_idemp_l (b * (M64 - 1)) (M64 - 8192) M64), Zplus_mod_idemp_l.
replace (b * (M64 - 1) + (M64 - 8192) + a) with ((a - b - 8192) + (b + 1) * M64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. unfold M64 in *; lia.
Qed.
Ltac zneg := repeat (first [ rewrite zcanon_sub_8192; [ | zlia | zlia | unfold M64; zlia ]
| rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]
| rewrite zcanon_negadd_r; [ | zlia | unfold M64; zlia ]
| rewrite zcanon_add_m8192; [ | unfold M64; zlia ] ]).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (cur nx csz nsz nnx ncn lcnt llast tcnt tfirst tlast tby tot lbytes : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33bf8) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Definition XW : list word :=
[ w64 cur; w64 nx; w64 csz; w64 nsz; w64 nnx; w64 ncn; w64 lcnt; w64 llast; w64 tcnt; w64 tfirst; w64 tlast; w64 tby; w64 tot; w64 lbytes ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma Eq32 : ew E0 32 = w64 cur. Proof. reflexivity. Qed.
Lemma Eq33 : ew E0 33 = w64 nx. Proof. reflexivity. Qed.
Lemma Eq34 : ew E0 34 = w64 csz. Proof. reflexivity. Qed.
Lemma Eq35 : ew E0 35 = w64 nsz. Proof. reflexivity. Qed.
Lemma Eq36 : ew E0 36 = w64 nnx. Proof. reflexivity. Qed.
Lemma Eq37 : ew E0 37 = w64 ncn. Proof. reflexivity. Qed.
Lemma Eq38 : ew E0 38 = w64 lcnt. Proof. reflexivity. Qed.
Lemma Eq39 : ew E0 39 = w64 llast. Proof. reflexivity. Qed.
Lemma Eq40 : ew E0 40 = w64 tcnt. Proof. reflexivity. Qed.
Lemma Eq41 : ew E0 41 = w64 tfirst. Proof. reflexivity. Qed.
Lemma Eq42 : ew E0 42 = w64 tlast. Proof. reflexivity. Qed.
Lemma Eq43 : ew E0 43 = w64 tby. Proof. reflexivity. Qed.
Lemma Eq44 : ew E0 44 = w64 tot. Proof. reflexivity. Qed.
Lemma Eq45 : ew E0 45 = w64 lbytes. Proof. reflexivity. Qed.
(* MergeBatches' frame (ra at +8) and the temp list's header (+16 .. +48); the global list's count, and its last and
   byte words (two regions, so that the list's first word +168, which the tail never writes, stays out of the window);
   cur's and nx's next / size / count words; the temp list's last batch's next word (when the temp list is not empty). *)
Definition R_STK : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 48 16 48
[YP09.mkChunk 8 (CVal 8 (SLit 0x33a38)); YP09.mkChunk 16 (CVal 8 (SOff 40%nat 0)); YP09.mkChunk 24 (CVal 8 (SOff 41%nat 0));
YP09.mkChunk 32 (CVal 8 (SOff 42%nat 0)); YP09.mkChunk 40 (CVal 8 (SOff 43%nat 0))].
Definition R_LH1 : YP09.region :=
YP09.mkRegion None (A_QUAR + 160) (A_QUAR + 168) (A_QUAR + 160) (A_QUAR + 168)
[YP09.mkChunk (A_QUAR + 160) (CVal 8 (SOff 38%nat 0))].
Definition R_LH2 : YP09.region :=
YP09.mkRegion None (A_QUAR + 176) (A_QUAR + 192) (A_QUAR + 176) (A_QUAR + 192)
[YP09.mkChunk (A_QUAR + 176) (CVal 8 (SOff 39%nat 0)); YP09.mkChunk (A_QUAR + 184) (CVal 8 (SOff 45%nat 0))].
Definition R_CUR : YP09.region := YP09.mkRegion (Some 32%nat) 0 24 0 24 [].
Definition R_NX : YP09.region :=
YP09.mkRegion (Some 33%nat) 0 24 0 24 [YP09.mkChunk 0 (CVal 8 (SOff 36%nat 0)); YP09.mkChunk 8 (CVal 8 (SOff 35%nat 0))].
Definition REG0 : smem := [ R_STK; R_LH1; R_LH2; R_CUR; R_NX ].
Definition R_TL : YP09.region := YP09.mkRegion (Some 42%nat) 0 8 0 8 [].
Definition FFT : facts := mkFacts
[ (2%nat, mkAF kHighMemBeg (kHighMemEnd - 48) 4);
(32%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(33%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(34%nat, mkAF 8192 (2 ^ 40) 0);
(35%nat, mkAF 8192 (2 ^ 40) 0);
(36%nat, mkAF 0 CEIL_MAX 13);
(37%nat, mkAF 0 1021 0);
(38%nat, mkAF 1 (2 ^ 40) 0);
(39%nat, mkAF 0 CEIL_MAX 13);
(40%nat, mkAF 0 (2 ^ 40) 0);
(41%nat, mkAF 0 CEIL_MAX 0);
(42%nat, mkAF 0 CEIL_MAX 13);
(43%nat, mkAF 0 (2 ^ 40) 0);
(44%nat, mkAF 0 (2 ^ 40) 0);
(45%nat, mkAF 0 (2 ^ 40) 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
10%bv (SLit (A_QUAR + 160))) 11%bv (SOff 2%nat 16)) 12%bv (SOff 44%nat 0)) 13%bv (SOff 34%nat 0))
14%bv (SOff 32%nat 0)) 5%bv (SOff 33%nat 0)) 6%bv (SOff 37%nat 0)) 15%bv (SLit 1021))
16%bv (SLit M8192)) 17%bv (SLit 8192).
Definition SS0 : sstate := mkSS 0x33bf8 SR0 REG0 None FFT.
Record free_hyps : Prop := FreeHyps {
fh_Hsp : kHighMemBeg <= sp0 /\ sp0 + 48 <= kHighMemEnd;
fh_Hsp_al : sp0 mod 16 = 0;
fh_Hcur : kHighMemBeg <= cur /\ cur + kBatchBytes <= ASAN_CEIL /\ cur mod 8192 = 0;
fh_Hnx : kHighMemBeg <= nx /\ nx + kBatchBytes <= ASAN_CEIL /\ nx mod 8192 = 0;
fh_Hsz : kBatchBytes <= csz <= 2 ^ 40 /\ kBatchBytes <= nsz <= 2 ^ 40;
fh_Hnnx : 0 <= nnx < ASAN_CEIL /\ nnx mod 8192 = 0;
fh_Hncn : 0 <= ncn <= kBatchSlots;
fh_Hl : 1 <= lcnt <= 2 ^ 40 /\ 0 <= llast < ASAN_CEIL /\ llast mod 8192 = 0;
fh_Ht : 0 <= tcnt < 2 ^ 40 /\ 0 <= tfirst < ASAN_CEIL /\ 0 <= tlast < ASAN_CEIL /\ tlast mod 8192 = 0;
fh_Htl : tcnt <> 0 -> kHighMemBeg <= tlast /\ tlast + kBatchBytes <= ASAN_CEIL /\
  (tlast + 8 <= cur \/ cur + 24 <= tlast) /\ (tlast + 8 <= nx \/ nx + 24 <= tlast) /\ (tlast + 8 <= sp0 \/ sp0 + 48 <= tlast) /\
  (forall a, tlast <= a < tlast + 8 -> apresent (w_H W) mem0 a);
fh_Hby : 0 <= tby <= 2 ^ 40 /\ 0 <= tot /\ tot + kBatchBytes <= lbytes <= 2 ^ 40;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x33bf8) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Hsp Hsp_al Hcur Hnx Hsz Hnnx Hncn Hl Ht Htl Hby SEED].
Lemma derived_ranges :
kHighMemBeg <= sp0 /\ sp0 + 48 <= kHighMemEnd /\
kHighMemBeg <= cur /\ cur + kBatchBytes <= ASAN_CEIL /\ kHighMemBeg <= nx /\ nx + kBatchBytes <= ASAN_CEIL /\
8192 <= csz <= 2 ^ 40 /\ 8192 <= nsz <= 2 ^ 40 /\ 0 <= nnx < ASAN_CEIL /\ 0 <= ncn <= 1021 /\
1 <= lcnt <= 2 ^ 40 /\ 0 <= llast < ASAN_CEIL /\ 0 <= tcnt < 2 ^ 40 /\ 0 <= tfirst < ASAN_CEIL /\ 0 <= tlast < ASAN_CEIL /\
0 <= tby <= 2 ^ 40 /\ 0 <= tot /\ tot + 8192 <= lbytes /\ lbytes <= 2 ^ 40 /\ ASAN_CEIL <= CEIL_MAX.
Proof.
open_FH. destruct Hsp as [S1 S2]. destruct Hcur as (C1 & C2 & _). destruct Hnx as (N1 & N2 & _). destruct Hsz as [Z1 Z2].
destruct Hnnx as (M1 & _). destruct Hl as (L1 & L2 & _). destruct Ht as (T1 & T2 & T3 & _). destruct Hby as (B1 & B2 & B3).
clear - S1 S2 C1 C2 N1 N2 Z1 Z2 M1 Hncn L1 L2 T1 T2 T3 B1 B2 B3. numconst. repeat split; lia.
Qed.
Definition WINF (a : Z) : Prop :=
(sp0 + 16 <= a < sp0 + 48) \/ (A_QUAR + 160 <= a < A_QUAR + 168) \/ (A_QUAR + 176 <= a < A_QUAR + 192) \/
(cur <= a < cur + 24) \/ (nx <= a < nx + 24).
Definition WINA (a : Z) : Prop := tcnt <> 0 /\ tlast <= a < tlast + 8.
Definition WIN (a : Z) : Prop := WINF a \/ WINA a.
Definition win_sub (t w : option nat * Z * Z) : bool :=
obase_eqb (fst (fst t)) (fst (fst w)) && (snd (fst w) <=? snd (fst t)) && (snd t <=? snd w).
Lemma win_sub_sound : forall E a t w, win_sub t w = true ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t ->
base_val E (fst (fst w)) + snd (fst w) <= a < base_val E (fst (fst w)) + snd w.
Proof.
intros E a [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. subst. lia.
- lia.
Qed.
Definition WSK0 : list (option nat * Z * Z) :=
[(Some 2%nat, 16, 48); (None, A_QUAR + 160, A_QUAR + 168); (None, A_QUAR + 176, A_QUAR + 192); (Some 32%nat, 0, 24);
(Some 33%nat, 0, 24)].
Definition WSKL : list (option nat * Z * Z) := WSK0 ++ [(Some 42%nat, 0, 8)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
open_FH. intros E HE t a Hin Hr. pose proof derived_ranges as DR. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN, WINF.
ceil; unfold kHighMemBeg, ASAN_CEIL, kBatchBytes, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by (cbv; lia); rewrite ?E2, ?Eq32, ?Eq33 in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Lemma WSKL_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> tcnt <> 0 -> sk_ok E WSKL.
Proof.
open_FH. intros E HE Hc t a Hin Hr. unfold WSKL in Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (WSK0_ok E HE t a Hin Hr)|].
pose proof derived_ranges as DR. cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr.
rewrite HE in Hr by (cbv; lia). rewrite Eq42 in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by (clear - DR; numconst; lia).
unfold WIN, WINA. right. split; [exact Hc | lia].
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b0 & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Definition SREGS : list (bv 5) := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition SREGSX : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition TFn : Z := if tcnt =? 0 then nx else tfirst.
Definition LLn : Z := if llast =? nx then cur else llast.
Definition tail_cells (m : word -> option byte) (lb : Z) : Prop :=
val_mem tfibsegs m cur 8 nnx /\ val_mem tfibsegs m (cur + 8) 8 (csz + nsz - 8192) /\ val_mem tfibsegs m (cur + 16) 8 ncn /\
val_mem tfibsegs m nx 8 0 /\ val_mem tfibsegs m (nx + 8) 8 8192 /\ val_mem tfibsegs m (nx + 16) 8 0 /\
val_mem tfibsegs m (A_QUAR + 160) 8 (lcnt - 1) /\ val_mem tfibsegs m (A_QUAR + 176) 8 LLn /\ val_mem tfibsegs m (A_QUAR + 184) 8 lb /\
val_mem tfibsegs m (sp0 + 16) 8 (tcnt + 1) /\ val_mem tfibsegs m (sp0 + 24) 8 TFn /\ val_mem tfibsegs m (sp0 + 32) 8 nx /\
val_mem tfibsegs m (sp0 + 40) 8 (tby + 8192) /\ (tcnt <> 0 -> val_mem tfibsegs m tlast 8 nx).
Definition at_TCONT (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ nnx <> 0 /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33bac) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (A_QUAR + 160) /\ getr regs' 11 = w64 (sp0 + 16) /\ getr regs' 12 = w64 (tot + 8192) /\
getr regs' 15 = w64 1021 /\ getr regs' 16 = w64 M8192 /\ getr regs' 17 = w64 8192 /\
getr regs' 14 = w64 cur /\ getr regs' 5 = w64 nnx /\
MEQ mem' /\ (forall a, WIN a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
tail_cells (mrestrict (w_H W) mem') lbytes.
Definition at_TEXIT (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ nnx = 0 /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33a38) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = w64 (sp0 + 16) /\ getr regs' 1 = w64 0x33a38 /\ (forall r : bv 5, In r SREGSX -> getr regs' r = getr regs0 r) /\
MEQ mem' /\ (forall a, WIN a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
tail_cells (mrestrict (w_H W) mem') (lbytes - (tot + 8192)).
Definition postT : world tfibsegs -> config -> Prop := if nnx =? 0 then at_TEXIT else at_TCONT.

Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac chunk_index cs off k :=
lazymatch cs with
| (YP09.mkChunk ?o _) :: ?t => let e := eval vm_compute in (o =? off) in
lazymatch e with true => k | false => chunk_index t off (S k) end
end.
Ltac memvo HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := eval cbv in (YP09.r_chunks rg) in
let j := chunk_index cs off 0%nat in memv HS i j end end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; zneg; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac tA := cbn [base_val YP09.r_base]; rewrite ?Z.add_0_l; first [ reflexivity | zlia | numconst; zlia
| match goal with B : bv_unsigned (ew _ 32) = _ |- _ => rewrite B end; zlia
| match goal with B : bv_unsigned (ew _ 33) = _ |- _ => rewrite B end; zlia
| match goal with B : bv_unsigned (ew _ 42) = _ |- _ => rewrite B end; zlia
| match goal with B : bv_unsigned (ew _ 2) = _ |- _ => rewrite B end; unfold sp0; zlia ].
Ltac zev_close := cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
unfold M8192 in *; zcanon_simp; zneg; zcanon_simp; zlia.
(* TFn / LLn are rewritten by the case equations in context (ETF / ELL); EQS is unused. *)
Ltac rw_tl := repeat match goal with E : TFn = _ |- context [TFn] => rewrite E | E : LLn = _ |- context [LLn] => rewrite E end.
Ltac tV EQS := first
[ reflexivity
| rw_tl; reflexivity
| cbn [sv_denot]; rewrite ?Eq32, ?Eq33, ?Eq34, ?Eq35, ?Eq36, ?Eq37, ?Eq38, ?Eq39, ?Eq40, ?Eq41, ?Eq42, ?Eq43, ?Eq44, ?Eq45;
unfold w64; rewrite ?Zbv_add_unsigned; rw_tl; first [ reflexivity | f_equal; zlia ]
| apply denot_by_zev; [ reflexivity | rw_tl; numconst; zlia | rw_tl; zev_close ] ].
Ltac tR EQS := first [ zlia | rw_tl; numconst; zlia | apply u64_range ].
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; reflexivity.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac reg_zev HS r :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot (w_H W) E0 _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
apply denot_by_zev; [ reflexivity | numconst; zlia | zev_close ].
Ltac reg_val HS r := first [ let Q := fresh "Q" in rreg HS r Q; rewrite Q; tV I | reg_zev HS r ].
Ltac reg_keep HS := lazymatch goal with |- getr _ ?r = getr _ _ =>
let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in reg_entry HS r k end.
Ltac sregs HS := intros r Hr; cbn [SREGS SREGSX In] in Hr;
repeat match type of Hr with
| _ = r \/ _ => let E := fresh "E" in destruct Hr as [E|Hr]; [subst r; reg_keep HS|]
| _ = r => subst r; reg_keep HS
| False => destruct Hr
end.
Ltac off_by tac := first [ apply off_img_high; tac | unfold off_img; unfold TFIB_IMG_LO; unfold TFIB_IMG_END; tac ].
(* presence of the windows above kHighMemBeg; the region indices: stack iS, cur iC, nx iN, temp last 0 (when present) *)
Ltac presT HS iS iC iN BV2 BV32 BV33 DR tTL :=
intros a Ha Hh; unfold WIN, WINF, WINA in Ha;
destruct Ha as [[Ha|[Ha|[Ha|[Ha|Ha]]]]|[Hne Ha]];
[ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iS _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold sp0 in *; clear - Ha; zlia | off_by ltac:(clear - Ha Hh DR; numconst; zlia) ]
| exfalso; clear - Ha Hh; numconst; zlia
| exfalso; clear - Ha Hh; numconst; zlia
| eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iC _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ]
| eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iN _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV33; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ]
| tTL Hne Ha ].
Ltac cellv HS i off := first [ memvo HS i off; [tA | tV I | tR I] | match goal with |- ?g => idtac "CELLFAIL" g; fail end ].
(* iG: the list count's region; the list last / bytes region is the next one *)
Ltac cells HS EQS iS iG iC iN tTLV :=
let iH := eval vm_compute in (S iG) in
unfold tail_cells;
split; [idtac "C1"; cellv HS iC 0|];
split; [idtac "C2"; cellv HS iC 8|];
split; [idtac "C3"; cellv HS iC 16|];
split; [idtac "C4"; cellv HS iN 0|];
split; [idtac "C5"; cellv HS iN 8|];
split; [idtac "C6"; cellv HS iN 16|];
split; [idtac "C7"; cellv HS iG (A_QUAR + 160)|];
split; [idtac "C8"; cellv HS iH (A_QUAR + 176)|];
split; [idtac "C9"; cellv HS iH (A_QUAR + 184)|];
split; [idtac "C10"; cellv HS iS 16|];
split; [idtac "C11"; cellv HS iS 24|];
split; [idtac "C12"; cellv HS iS 32|];
split; [idtac "C13"; cellv HS iS 40|];
idtac "C14"; tTLV.
Ltac fin_cont HS EQS iS iG iC iN tPRES tTLV :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [assumption|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [rewrite HshR at 1; reflexivity|];
split; [reg_entry HS (2%bv : bv 5) 2%nat|];
split; [sregs HS|];
split; [first [reg_lit HS (10%bv : bv 5) | reg_val HS (10%bv : bv 5)]|];
split; [let Q := fresh "Q" in rreg HS (11%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; zlia|];
split; [reg_val HS (12%bv : bv 5)|];
split; [reg_val HS (15%bv : bv 5)|];
split; [reg_val HS (16%bv : bv 5)|];
split; [reg_val HS (17%bv : bv 5)|];
split; [reg_val HS (14%bv : bv 5)|];
split; [reg_val HS (5%bv : bv 5)|];
split; [assumption|];
split; [tPRES|];
cells HS EQS iS iG iC iN tTLV
end.
Ltac fin_exit HS EQS iS iG iC iN tPRES tTLV :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [assumption|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [rewrite HshR at 1; reflexivity|];
split; [let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; zlia|];
split; [reg_lit HS (1%bv : bv 5)|];
split; [sregs HS|];
split; [assumption|];
split; [tPRES|];
cells HS EQS iS iG iC iN tTLV
end.
(* the last branch (0x33c8c bnez next(cur)) and the two ends *)
Ltac tail_end HS SKW EQS iS iG iC iN tPRES tTLV DR R36 :=
srr_branch_sh tfibtbl_rtG_ok HS;
[ let HN := fresh "HNN" in
  match goal with Hb : branch_taken _ _ _ = true |- _ =>
  assert (HN : nnx <> 0) by (clear - Hb DR R36; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.eqb_neq in Hb; exact Hb); clear Hb end;
  unfold postT; destruct (Z.eqb_spec nnx 0) as [X|_]; [exfalso; exact (HN X)|];
  unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
  srr_run_to_sh tfibtbl_rtG_ok HS 0x33bac; meq_acc SKW;
  fin_cont HS EQS iS iG iC iN tPRES tTLV
| let HN := fresh "HNN" in
  match goal with Hb : branch_taken _ _ _ = false |- _ =>
  assert (HN : nnx = 0) by (clear - Hb DR R36; zbranch Hb; apply Bool.negb_false_iff in Hb; apply Z.eqb_eq in Hb; exact Hb); clear Hb end;
  unfold postT; destruct (Z.eqb_spec nnx 0) as [_|X]; [|exfalso; exact (X HN)];
  unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
  srr_run_to_sh tfibtbl_rtG_ok HS 0x33a38; meq_acc SKW;
  fin_exit HS EQS iS iG iC iN tPRES tTLV ].
(* the temp-list test (polarity depends on the path); [HNP] fixes tcnt = 0 or tcnt <> 0 *)
Ltac zt_contra Hb HNP DR R40 :=
clear - Hb DR R40 HNP; zbranch Hb;
first [ apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb | apply Bool.negb_true_iff in Hb; apply Z.eqb_neq in Hb
      | apply Bool.negb_false_iff in Hb; apply Z.eqb_eq in Hb ]; zlia.
Ltac tcnt_step HS SKW HNP DR R40 tcont :=
srr_branch_sh tfibtbl_rtG_ok HS;
[ first [ exfalso; match goal with Hb : branch_taken _ _ _ = true |- _ => zt_contra Hb HNP DR R40 end
        | match goal with Hb : branch_taken _ _ _ = true |- _ => clear Hb end;
          unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
          srr_run_sh tfibtbl_rtG_ok HS; meq_acc SKW; tcont ]
| first [ exfalso; match goal with Hb : branch_taken _ _ _ = false |- _ => zt_contra Hb HNP DR R40 end
        | match goal with Hb : branch_taken _ _ _ = false |- _ => clear Hb end;
          unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
          srr_run_sh tfibtbl_rtG_ok HS; meq_acc SKW; tcont ] ].

Lemma segT : SRr tfibsegs W cfg0 postT.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof derived_ranges as DR.
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
assert (R32 : rho_of E0 32%nat = cur) by (unfold rho_of; rewrite Eq32; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R33 : rho_of E0 33%nat = nx) by (unfold rho_of; rewrite Eq33; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R34 : rho_of E0 34%nat = csz) by (unfold rho_of; rewrite Eq34; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R35 : rho_of E0 35%nat = nsz) by (unfold rho_of; rewrite Eq35; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R36 : rho_of E0 36%nat = nnx) by (unfold rho_of; rewrite Eq36; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R37 : rho_of E0 37%nat = ncn) by (unfold rho_of; rewrite Eq37; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R38 : rho_of E0 38%nat = lcnt) by (unfold rho_of; rewrite Eq38; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R39 : rho_of E0 39%nat = llast) by (unfold rho_of; rewrite Eq39; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R40 : rho_of E0 40%nat = tcnt) by (unfold rho_of; rewrite Eq40; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R41 : rho_of E0 41%nat = tfirst) by (unfold rho_of; rewrite Eq41; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R42 : rho_of E0 42%nat = tlast) by (unfold rho_of; rewrite Eq42; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R43 : rho_of E0 43%nat = tby) by (unfold rho_of; rewrite Eq43; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R44 : rho_of E0 44%nat = tot) by (unfold rho_of; rewrite Eq44; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R45 : rho_of E0 45%nat = lbytes) by (unfold rho_of; rewrite Eq45; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (BV32 : bv_unsigned (ew E0 32) = cur) by exact R32.
assert (BV33 : bv_unsigned (ew E0 33) = nx) by exact R33.
assert (BV42 : bv_unsigned (ew E0 42) = tlast) by exact R42.
destruct (Z.eq_dec tcnt 0) as [HNP|HNP].
- (* the temp list is empty *)
pose proof (WSK0_ok E0 HE0) as SKW.
assert (ETF : TFn = nx) by (unfold TFn; rewrite HNP, Z.eqb_refl; reflexivity).
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
+ assert (HLL : llast = nx) by (clear - Hc DR R33 R39; zbranch Hc; apply Z.eqb_eq in Hc; exact Hc). clear Hc.
assert (ELL : LLn = cur) by (unfold LLn; rewrite HLL, Z.eqb_refl; reflexivity).
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
tcnt_step HS SKW HNP DR R40 ltac:(tail_end HS SKW (conj ETF ELL) 0%nat 1%nat 3%nat 4%nat
  ltac:(presT HS 0%nat 3%nat 4%nat BV2 BV32 BV33 DR ltac:(fun Hne Ha => exfalso; exact (Hne HNP)))
  ltac:(intros X; exfalso; exact (X HNP)) DR R36).
+ assert (HLL : llast <> nx) by (clear - Hc DR R33 R39; zbranch Hc; apply Z.eqb_neq in Hc; exact Hc). clear Hc.
assert (ELL : LLn = llast) by (unfold LLn; destruct (Z.eqb_spec llast nx); [exfalso; exact (HLL e) | reflexivity]).
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
tcnt_step HS SKW HNP DR R40 ltac:(tail_end HS SKW (conj ETF ELL) 0%nat 1%nat 3%nat 4%nat
  ltac:(presT HS 0%nat 3%nat 4%nat BV2 BV32 BV33 DR ltac:(fun Hne Ha => exfalso; exact (Hne HNP)))
  ltac:(intros X; exfalso; exact (X HNP)) DR R36).
- (* the temp list is not empty: its last batch's next word is a region *)
destruct (Htl HNP) as (L1 & L2 & L3 & L4 & L5 & L6).
apply (st_ok_add_region _ _ _ R_TL) in HS;
[ | reflexivity
| unfold R_TL, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV42;
  split; [clear - L1 DR; numconst; zlia|]; split; [clear - L1 L2 DR; numconst; zlia|];
  split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - L1 L2 DR Ho; numconst; zlia) | apply L6; zlia] |];
  apply Forall_nil
| unfold R_TL; cbn [YP09.all_disjoint ss_mem]; repeat split; unfold YP09.extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV33, ?BV42, ?BV2; unfold sp0 in *; clear - DR L1 L2 L3 L4 L5; numconst; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof (WSKL_ok E0 HE0 HNP) as SKW.
assert (ETF : TFn = tfirst) by (unfold TFn; destruct (Z.eqb_spec tcnt 0); [exfalso; exact (HNP e) | reflexivity]).
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
+ assert (HLL : llast = nx) by (clear - Hc DR R33 R39; zbranch Hc; apply Z.eqb_eq in Hc; exact Hc). clear Hc.
assert (ELL : LLn = cur) by (unfold LLn; rewrite HLL, Z.eqb_refl; reflexivity).
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
tcnt_step HS SKW HNP DR R40 ltac:(tail_end HS SKW (conj ETF ELL) 1%nat 2%nat 4%nat 5%nat
  ltac:(presT HS 1%nat 4%nat 5%nat BV2 BV32 BV33 DR
    ltac:(fun Hne Ha => eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV42; clear - Ha; zlia | off_by ltac:(clear - Ha L1 L2 DR; numconst; zlia) ]))
  ltac:(intros _; memvo HS 0%nat 0; [tA | tV I | tR I]) DR R36).
+ assert (HLL : llast <> nx) by (clear - Hc DR R33 R39; zbranch Hc; apply Z.eqb_neq in Hc; exact Hc). clear Hc.
assert (ELL : LLn = llast) by (unfold LLn; destruct (Z.eqb_spec llast nx); [exfalso; exact (HLL e) | reflexivity]).
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
tcnt_step HS SKW HNP DR R40 ltac:(tail_end HS SKW (conj ETF ELL) 1%nat 2%nat 4%nat 5%nat
  ltac:(presT HS 1%nat 4%nat 5%nat BV2 BV32 BV33 DR
    ltac:(fun Hne Ha => eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV42; clear - Ha; zlia | off_by ltac:(clear - Ha L1 L2 DR; numconst; zlia) ]))
  ltac:(intros _; memvo HS 0%nat 0; [tA | tV I | tR I]) DR R36).
Qed.
End WK.
End d.
