(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Definition IBx : sv := SOff 22 0.
Definition I_stack : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 96 0 96 (map (fun j => YP09.mkChunk (88 - 8 * Z.of_nat j) (CVal 8 (SOff (36 + j)%nat 0))) (seq 0 12)).
Definition I_st (curv : sv) : YP09.region := st_region 19 (SOff 32 0) (SOff 33 0) curv.
Definition I_cfg_tail : list YP09.chunk :=
[YP09.mkChunk 8 (CZero 8); YP09.mkChunk 16 (CVal 4 (SOff 48 0)); YP09.mkChunk 20 (CVal 4 (SOff 49 0)); YP09.mkChunk 24 (CVal 2 (SOff 50 0));
YP09.mkChunk 26 (CVal 2 (SOff 51 0)); YP09.mkChunk 28 (CVal 1 (SOff 52 0))].
Definition I_dst (c0 : sv) : YP09.region := YP09.mkRegion (Some 8%nat) 0 32 0 16 (YP09.mkChunk 0 (CVal 8 c0) :: I_cfg_tail).
Definition I_facts : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 4096 0x7fffff800000 3); (18%nat, mkAF 1 100000000 0); (19%nat, mkAF (2^46) (2^47 - 24) 3);
(22%nat, mkAF SB SB 0); (32%nat, mkAF 4096 0x7fffff800000 4); (33%nat, mkAF 1 (2^28) 0); (34%nat, mkAF 0 (2^28) 0);
(48%nat, mkAF 0 (2^32 - 1) 0); (49%nat, mkAF 0 (2^32 - 1) 0); (50%nat, mkAF 0 65535 0); (51%nat, mkAF 0 65535 0); (52%nat, mkAF 0 255 0) ].
Definition rfc_regions : list YP09.region := [I_stack; got_region; bcell_region 22; I_dst (SOff 35 0); I_st (SOff 34 0)].
Definition rfc_regions_d (rd : YP09.region) : list YP09.region := [I_stack; got_region; bcell_region 22; rd; I_st (SOff 34 0)].
Definition I_sh (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 k) (SLit 3)) IBx.
Definition I_regs : list sv := sr_set (sr_set (sr_set (sr_set sr_atoms 9%bv (SOff 19 16)) 20%bv (SOff 19 8)) 23%bv (I_sh 16)) 24%bv (I_sh 8).
Definition ss_I : sstate := mkSS RFC_I I_regs rfc_regions None (mkFacts I_facts [] []).
Definition ss_I_c : sstate := Eval vm_compute in ss_I.
Definition J_regs : list sv := sr_set I_regs 21%bv (SOff 8 26).
Definition ss_J : sstate := mkSS RFC_J J_regs rfc_regions None (mkFacts I_facts [] []).
Definition ss_J_c : sstate := Eval vm_compute in ss_J.
Definition C3_dst : YP09.region := YP09.mkRegion (Some 8%nat) 0 32 0 32 (YP09.mkChunk 0 (CVal 8 (SOff 35 0)) :: I_cfg_tail).
Definition C3_regs : list sv := sr_set (sr_set I_regs 10%bv (SOff 8 16)) 14%bv (SAlu ALU_SRL (SOff 8 16) (SLit 3)).
Definition ss_C3 : sstate := mkSS RFC_RD3 C3_regs (rfc_regions_d C3_dst) None (mkFacts I_facts [] []).
Definition ss_C3_c : sstate := Eval vm_compute in ss_C3.
Definition ss_C1 : sstate := mkSS RFC_RD1 C3_regs (rfc_regions_d C3_dst) None (mkFacts I_facts [] []).
Definition ss_C1_c : sstate := Eval vm_compute in ss_C1.
Definition I_extra (regs : bvmap 5 word) (pdata nb curv lpa fattr fgen delay nlp tidx : Z) : list word :=
map (Z_to_bv 64) [pdata; nb; curv; lpa] ++ map (fun r => getr regs (Z_to_bv 5 r)) rfc_saved ++ map (Z_to_bv 64) [fattr; fgen; delay; nlp; tidx].
Definition rfc_vals (racc curv lpa nlp fattr fgen delay tidx cur nb : Z) : Prop :=
0 <= racc < 2 ^ 64 /\ cur <= curv <= nb /\ 0 <= lpa < 2 ^ 64 /\ 0 <= nlp < 2 ^ 16 /\
0 <= fattr < 2 ^ 32 /\ 0 <= fgen < 2 ^ 32 /\ 0 <= delay < 2 ^ 16 /\ 0 <= tidx < 2 ^ 8.
Definition rfc_memI (m : word -> option byte) (st dst pdata nb curv lpa fattr fgen delay nlp tidx : Z) : Prop :=
val_mem tfibsegs m st 8 pdata /\ val_mem tfibsegs m (st + 8) 8 nb /\ val_mem tfibsegs m (st + 16) 8 curv /\
val_mem tfibsegs m dst 8 lpa /\ val_mem tfibsegs m (dst + 8) 8 0 /\ val_mem tfibsegs m (dst + 16) 4 fattr /\ val_mem tfibsegs m (dst + 20) 4 fgen /\
val_mem tfibsegs m (dst + 24) 2 delay /\ val_mem tfibsegs m (dst + 26) 2 nlp /\ val_mem tfibsegs m (dst + 28) 1 tidx.
Definition hb (P : list Z) (cur j : Z) : Z := nth (Z.to_nat (cur + j)) P 0.
Definition rfc_hdrv (P : list Z) (cur nb fattr fgen delay tidx nlp : Z) : Prop :=
cur + 9 <= nb -> fattr = hb P cur 0 + 256 * hb P cur 1 /\ fgen = hb P cur 2 + 256 * hb P cur 3 /\ delay = hb P cur 4 + 256 * hb P cur 5 /\
tidx = hb P cur 6 /\ nlp = hb P cur 7 + 256 * hb P cur 8.
Definition palsz (fattr nlp : Z) : Z := if Z.land fattr 1 =? 0 then 0 else 3 * nlp.
Definition rfc_progH (cur nb R curv : Z) : Prop := (R = 0 /\ cur + 9 <= nb /\ curv = cur + 9) \/ (R <> 0 /\ nb < cur + 9 /\ curv = nb).
Definition rfc_progPJ (P : list Z) (m : word -> option byte) (cur nb nlp R r1 cur2 res : Z) : Prop :=
(Z.lor r1 R = 0 /\ cur + 9 + 3 * nlp <= nb /\ cur2 = cur + 9 + 3 * nlp /\
garr8 tfibsegs m res (firstn (Z.to_nat (3 * nlp)) (skipn (Z.to_nat (cur + 9)) P)))
\/ (Z.lor r1 R <> 0 /\ nb < cur + 9 + 3 * nlp /\ cur2 = nb).
Definition rfc_progP (P : list Z) (m : word -> option byte) (cur nb fattr nlp R curv lpa : Z) : Prop :=
(R = 0 /\ cur + 9 + palsz fattr nlp <= nb /\ curv = cur + 9 + palsz fattr nlp /\
(Z.land fattr 1 <> 0 -> garr8 tfibsegs m lpa (firstn (Z.to_nat (3 * nlp)) (skipn (Z.to_nat (cur + 9)) P))))
\/ (R <> 0 /\ nb < cur + 9 + palsz fattr nlp /\ curv = nb).
Definition rfc_progI (P : list Z) (m : word -> option byte) (cur nb fattr nlp N R curv lpa r1 cur2 img : Z) : Prop :=
(R = 0 /\ r1 = 0 /\ cur + 9 + palsz fattr nlp + N <= nb /\ cur2 = cur + 9 + palsz fattr nlp + N /\
(Z.land fattr 1 <> 0 -> garr8 tfibsegs m lpa (firstn (Z.to_nat (3 * nlp)) (skipn (Z.to_nat (cur + 9)) P))) /\
garr8 tfibsegs m img (firstn (Z.to_nat N) (skipn (Z.to_nat (cur + 9 + palsz fattr nlp)) P)))
\/ (Z.lor r1 R <> 0 /\ nb < cur + 9 + palsz fattr nlp + N /\ cur2 = nb).
Definition RFC_COST (MT : ameter_ops) (N : Z) : Z := mo_malloc MT 196605 + mo_malloc MT N + (mo_free MT + mo_free MT).
Lemma garr8_kept : forall (m m' : word -> option byte) base l,
(forall i, 0 <= i < Z.of_nat (length l) -> mbyte tfibsegs m' (base + i) = mbyte tfibsegs m (base + i)) ->
garr8 tfibsegs m base l -> garr8 tfibsegs m' base l.
Proof.
intros m m' base l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk1. destruct k; [|cbn in Hk1; lia]. specialize (Hv 0%nat Hk1). cbn [Z.of_nat] in Hv |- *. rewrite Z.add_0_r in Hv |- *. rewrite (Hk (Z.of_nat j)) by lia. exact Hv.
Qed.
Lemma garr8_kept_aview : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
(forall i, 0 <= i < Z.of_nat (length l) -> aview tfibsegs H' m' (base + i) = aview tfibsegs H m (base + i)) ->
garr8 tfibsegs (mrestrict H m) base l -> garr8 tfibsegs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l Hk. apply garr8_kept. intros i Hi. apply (mbyte_of_aview tfibsegs). exact (Hk i Hi).
Qed.
Lemma slice_nth : forall (P : list Z) (c : Z) (n j : nat),
(j < length (firstn n (skipn (Z.to_nat c) P)))%nat -> nth j (firstn n (skipn (Z.to_nat c) P)) 0 = nth (Z.to_nat c + j) P 0.
Proof.
intros P c n j Hj. rewrite length_firstn in Hj. rewrite nth_firstn. rewrite (proj2 (Nat.ltb_lt _ _)) by lia. apply nth_skipn.
Qed.
Lemma hb_slice : forall P cur j, 0 <= cur -> 0 <= j -> hb P cur j = nth (Z.to_nat cur + Z.to_nat j) P 0.
Proof. intros P cur j Hc Hj. unfold hb. f_equal. lia. Qed.
Lemma garr8_aview : forall (H : word -> bool) (m : word -> option byte) b l,
garr8 tfibsegs (mrestrict H m) b l -> forall j, (j < length l)%nat -> aview tfibsegs H m (b + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m b l Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite !(Z.mod_small (nth j l 0) 256 Hr). reflexivity.
Qed.
Lemma garr8_of_aview : forall (H : word -> bool) (m : word -> option byte) b l,
(forall j, (j < length l)%nat -> aview tfibsegs H m (b + Z.of_nat j) = Some (nth j l 0)) -> garr8 tfibsegs (mrestrict H m) b l.
Proof.
intros H m b l Ha j Hj. destruct (aview_byte tfibsegs H m _ _ (Ha j Hj)) as (bt & Hmb & Hv & Hr). split; [|exact Hr].
intros k Hk. destruct k; [|cbn in Hk; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hmb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite !(Z.mod_small (nth j l 0) 256 Hr), Hv. reflexivity.
Qed.
Lemma denot_srl3 : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 ->
sv_denot E (SAlu ALU_SRL (SOff n c) (SLit 3)) = Z_to_bv 64 ((v + c) / 8).
Proof.
intros E n c v Hn Hv Hc0 Hc.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_SRL (SOff n c) (SLit 3)))). f_equal.
change (U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn. rewrite !unsigned_lit_small by lia.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (v + c)) by lia. rewrite zcanon_small by lia. reflexivity.
Qed.
Definition src_region (q s : nat) : YP09.region :=
  YP09.mkRegion (Some q) 0 (Z.of_nat s) 0 0 (map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (S q + i) 0))) (seq 0 s)).
Lemma src_region_ok : forall E m q s base (bytes : nat -> Z),
  bv_unsigned (ew E q) = base -> 0 <= base -> base + Z.of_nat s <= 2 ^ 64 ->
  (forall i, (i < s)%nat -> ew E (S q + i) = Z_to_bv 64 (bytes i) /\ 0 <= bytes i < 256 /\ val_mem tfibsegs m (base + Z.of_nat i) 1 (bytes i)) ->
  region_ok tfibsegs E m (src_region q s).
Proof.
intros E m q s base bytes Hb H0 H1 Hi. unfold src_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (i & <- & Hin). apply in_seq in Hin.
destruct (Hi i ltac:(lia)) as (He & Hr & Hv).
apply (chunk_ok_val tfibsegs E m base (Z.of_nat i) 1 (SOff (S q + i) 0) (bytes i)).
- cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- cbn. lia.
- cbn. lia.
- exact Hv.
Qed.
Lemma st_ok_cut : forall k E ss ms,
st_ok tfibsegs E ss ms -> ss_resv ss = None -> ss_atoms_lt k ss = true -> mem_atoms_lt k (ss_mem ss) = true ->
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms)) CLOB))
(mkSS (ss_pc ss) (sr_sets (ss_regs ss) (junk_upd k CLOB)) (ss_mem ss) None (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss))))
(mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfibsegs)).
Proof.
intros k E ss ms HS Hrv Hat Hmat.
pose proof (st_ok_mkst tfibsegs E ss ms HS Hrv) as Hshape. rewrite Hshape in HS.
pose proof (st_ok_splice_havoc tfibsegs k E ss (ms_regs ms) (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ss_pc ss) (ms_mem ms) (ms_mem ms) (ss_mem ss) [] CLOB HS Hat
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl Hmat ltac:(intros; reflexivity) ltac:(constructor) (st_ok_mem_ok tfibsegs E ss _ HS)) as H.
cbn [map app] in H.
pose proof (st_ok_facts_ok tfibsegs _ _ _ H) as (HA & HC & HL).
exact (st_ok_set_facts tfibsegs _ _ _ (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss))) H ltac:(split; [exact HA | split; [exact I | exact HL]])).
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Definition rfc_cx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(k : Z) (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur cid pos : Z) (T : Z) (P : list Z) : Prop :=
(mo_ok MT Sc T /\ RFC_COST MT N <= T /\ Z.of_nat (length P) = nb) /\
Permutation (ablocks B lyc Sc) Bb /\ In (pdata, nb) Bb /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - TRFC_STK /\ spZ regs <= sp0 /\
In (cid, pos) own /\ In (cid, pos) (frames Sc) /\ 0 <= cid /\ frame_addr lyc cid pos mod 8 = 0 /\
spZ regs <= st /\ st + 24 <= sp0 /\
frame_addr lyc cid pos <= dst /\ dst + 32 <= frame_addr lyc cid pos + fs_frame_bytes cid /\
rboxed (st + 24 <= dst \/ dst + 32 <= st) /\ st mod 8 = 0 /\ dst mod 8 = 0 /\
1 <= N <= 100000000 /\ 0 <= cur <= nb /\ 0 < nb /\
rfc_sep (spZ regs) Bb lyc Sc st dst /\ ly_F lyc = ly_F ly /\
st_nev S + k + EV_RFC <= EV_MAX /\ blocks_bytes Sc + LIVE_RFC <= LIVE_MAX /\
(4096 <= frame_addr lyc cid pos /\ (frame_addr lyc cid pos + fs_frame_bytes cid <= 65536 \/ 6270976 <= frame_addr lyc cid pos)
/\ (frame_addr lyc cid pos + fs_frame_bytes cid <= 2147446784 \/ 17594333495296 <= frame_addr lyc cid pos))
/\ frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling /\
(4096 <= pdata /\ (pdata + req_size nb <= 65536 \/ 6270976 <= pdata) /\ (pdata + req_size nb <= 2147446784 \/ 17594333495296 <= pdata))
/\ pdata + req_size nb <= alloc_ceiling /\ nb < 2 ^ 28.
Definition rfc_pal (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z)) (Bb pal : list (Z * Z))
(lpa nlp fattr : Z) : Prop :=
pal = (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) /\ (Z.land fattr 1 = 0 -> lpa = 0) /\
(forall b, In b pal -> aftok FP (ablocks B ly S) b /\
forall lyq blc i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (fst b + i)) /\
(forall b m, In (b, m) pal -> 4096 <= b /\ ~ In (b, m) Bb).
Definition rfc_post (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem0 md0 (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(Bb : list (Z * Z)) (st dst N pdata nb cur : Z) (lyc : alayout) (Sc : astate) (W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (P : list Z)
: world tfibsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res cur2 : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_RFC) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
getr regs2 10 = w64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - TRFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> aview tfibsegs (w_H W2) mem2 (b + i) = aview tfibsegs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memc a) /\
(forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memc a) /\
same_io mdc md2 /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) st 8 pdata /\ val_mem tfibsegs (mrestrict (w_H W2) mem2) (st + 8) 8 nb /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (st + 16) 8 cur2 /\ cur <= cur2 <= nb /\
mo_le MT Sc S2 (RFC_COST MT N) /\
((res = 0 /\ fst (fst (parse_frameN N (skipn (Z.to_nat cur) P))) = false /\ Permutation (ablocks B ly2 S2) Bb) \/
(res = 1 /\ exists lpal lpa img fattr fgen delay nlp tidx (LPAL IMG : list Z),
obj_at tfibsegs (mrestrict (w_H W2) mem2) dst LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
(Z.land fattr 1 = 0 -> lpal = 0) /\
Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (ablocks B ly2 S2) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ Bb) /\
(forall b, In b ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) ->
aftok FP (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (fst b + i)) /\
parse_frameN N (skipn (Z.to_nat cur) P) = (true, (fattr, fgen, delay, tidx, nlp, LPAL, IMG), skipn (Z.to_nat cur2) P) /\
garr8 tfibsegs (mrestrict (w_H W2) mem2) img IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 tfibsegs (mrestrict (w_H W2) mem2) lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp))).
Definition trfc_specX : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bb : list (Z * Z))
(st dst N pdata nb cur : Z) (cid pos : Z) ch (T : Z) (P : list Z),
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall b, In b (ablocks B ly S) -> In b Bb) -> Permutation (ablocks B lyc Sc) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 st -> getr regs 11 = w64 dst -> getr regs 12 = w64 N ->
achain lyc (aview tfibsegs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX_read_frameconfig ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRFC_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos mod 8 = 0 ->
frame_addr lyc cid pos <= dst -> dst + 32 <= frame_addr lyc cid pos + fs_frame_bytes cid -> dst mod 8 = 0 ->
spZ regs <= st -> st + 24 <= sp0 -> st mod 8 = 0 ->
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF st 24 ->
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF dst 32 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
val_mem tfibsegs (mrestrict (w_H W) memc) st 8 pdata -> val_mem tfibsegs (mrestrict (w_H W) memc) (st + 8) 8 nb ->
val_mem tfibsegs (mrestrict (w_H W) memc) (st + 16) 8 cur ->
st_nev S + k + EV_RFC <= EV_MAX -> blocks_bytes Sc + LIVE_RFC <= LIVE_MAX ->
garr8 tfibsegs (mrestrict (w_H W) memc) pdata P -> Z.of_nat (length P) = nb ->
mo_ok MT Sc T -> RFC_COST MT N <= T ->
SRr tfibsegs W (cfg_at tfibsegs A_read_frameconfig regs memc mdc)
(rfc_post STK sp0 FP ly S W0 mem0 md0 own k regs Bb st dst N pdata nb cur lyc Sc W memc mdc P).
Definition I_regs_at (regs regs1 : bvmap 5 word) (st dst N racc : Z) : Prop :=
getr regs1 2 = w64 (spZ regs - 96) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 dst /\ getr regs1 18 = w64 N /\ getr regs1 19 = w64 st /\ getr regs1 25 = w64 racc /\ getr regs1 22 = w64 SB /\
getr regs1 9 = w64 (st + 16) /\ getr regs1 20 = w64 (st + 8) /\ getr regs1 23 = w64 (SB + (st + 16) / 8) /\ getr regs1 24 = w64 (SB + (st + 8) / 8) /\
getr regs1 27 = getr regs 27.
Definition J_regs_at (regs regs1 : bvmap 5 word) (st dst N racc fb : Z) : Prop :=
I_regs_at regs regs1 st dst N racc /\ getr regs1 21 = w64 (dst + 26) /\ getr regs1 10 = w64 fb.
Definition C3_regs_at (regs regs1 : bvmap 5 word) (st dst N r1 r2 r3 cur3 : Z) : Prop :=
I_regs_at regs regs1 st dst N (bv_unsigned (getr regs1 25)) /\ getr regs1 10 = w64 (dst + 16) /\ getr regs1 14 = w64 ((dst + 16) / 8) /\
getr regs1 15 = w64 r1 /\ getr regs1 16 = w64 r2 /\ getr regs1 17 = w64 r3 /\ getr regs1 13 = w64 cur3.
Definition hdr3 (P : list Z) (cur nb r1 r2 r3 cur2 cur3 fattr fgen delay : Z) : Prop :=
(r1 = 0 \/ r1 = 2 ^ 64 - 1) /\ (r2 = 0 \/ r2 = 2 ^ 64 - 1) /\ (r3 = 0 \/ r3 = 2 ^ 64 - 1) /\
((Z.lor (Z.lor r1 r2) r3 = 0 /\ cur + 6 <= nb /\ cur3 = cur + 6 /\
fattr = hb P cur 0 + 256 * hb P cur 1 /\ fgen = hb P cur 2 + 256 * hb P cur 3 /\ delay = hb P cur 4 + 256 * hb P cur 5)
\/ (Z.lor (Z.lor r1 r2) r3 <> 0 /\ nb < cur + 6 /\ cur3 = nb)) /\
cur <= cur2 <= nb /\ 0 <= fattr < 2 ^ 16 /\ 0 <= fgen < 2 ^ 16 /\ 0 <= delay < 2 ^ 16.
Definition C1_regs_at (regs regs1 : bvmap 5 word) (st dst N r1 cur1 : Z) : Prop :=
I_regs_at regs regs1 st dst N (bv_unsigned (getr regs1 25)) /\ getr regs1 10 = w64 (dst + 16) /\ getr regs1 14 = w64 ((dst + 16) / 8) /\
getr regs1 15 = w64 r1 /\ getr regs1 13 = w64 cur1.
Definition hdr1 (P : list Z) (cur nb r1 cur1 fattr : Z) : Prop :=
(r1 = 0 \/ r1 = 2 ^ 64 - 1) /\
((r1 = 0 /\ cur + 2 <= nb /\ cur1 = cur + 2 /\ fattr = hb P cur 0 + 256 * hb P cur 1) \/ (r1 <> 0 /\ nb < cur + 2 /\ cur1 = nb)) /\
0 <= fattr < 2 ^ 16.
Definition RFC_I_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur cid pos : Z)
W1 (regs1 : bvmap 5 word) mem1 md1 ly1 S1 k1 (racc curv lpa nlp fattr fgen delay tidx : Z) (pal : list (Z * Z)) (T acc : Z) (P : list Z),
rfc_cx STK sp0 FP ly S own lyc Sc k regs Bb st dst N pdata nb cur cid pos T P ->
garr8 tfibsegs (mrestrict (w_H W) memc) pdata P ->
mo_le MT Sc S1 acc -> acc <= mo_malloc MT 196605 ->
rfc_hdrv P cur nb fattr fgen delay tidx nlp -> rfc_progP P (mrestrict (w_H W1) mem1) cur nb fattr nlp racc curv lpa ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k1 -> k <= k1 <= k + 1 -> frames S1 = frames Sc ->
Permutation (ablocks B ly1 S1) (pal ++ Bb) ->
rfc_pal STK sp0 FP ly S own Bb pal lpa nlp fattr ->
rfc_vals racc curv lpa nlp fattr fgen delay tidx cur nb ->
I_regs_at regs regs1 st dst N racc ->
rfc_frame (mrestrict (w_H W1) mem1) (spZ regs) regs ->
rfc_memI (mrestrict (w_H W1) mem1) st dst pdata nb curv lpa fattr fgen delay nlp tidx ->
range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF dst 32 ->
rfc_kept B W memc W1 mem1 (spZ regs) Bb lyc Sc st dst -> same_io mdc md1 ->
SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 RFC_I) mem1 (seg_rom tfibsegs)) md1)
(rfc_post STK sp0 FP ly S W0 mem0 md0 own k regs Bb st dst N pdata nb cur lyc Sc W memc mdc P).
Definition RFC_J_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur cid pos : Z)
W1 (regs1 : bvmap 5 word) mem1 md1 (racc curv nlp fattr fgen delay tidx : Z) (T : Z) (P : list Z),
rfc_cx STK sp0 FP ly S own lyc Sc k regs Bb st dst N pdata nb cur cid pos T P ->
garr8 tfibsegs (mrestrict (w_H W) memc) pdata P ->
rfc_hdrv P cur nb fattr fgen delay tidx nlp -> rfc_progH cur nb racc curv ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W1 mem1 md1 k ->
rfc_vals racc curv 0 nlp fattr fgen delay tidx cur nb ->
J_regs_at regs regs1 st dst N racc (Z.land fattr 1) ->
rfc_frame (mrestrict (w_H W1) mem1) (spZ regs) regs ->
rfc_memI (mrestrict (w_H W1) mem1) st dst pdata nb curv 0 fattr fgen delay nlp tidx ->
range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF dst 32 ->
rfc_kept B W memc W1 mem1 (spZ regs) Bb lyc Sc st dst -> same_io mdc md1 ->
SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 RFC_J) mem1 (seg_rom tfibsegs)) md1)
(rfc_post STK sp0 FP ly S W0 mem0 md0 own k regs Bb st dst N pdata nb cur lyc Sc W memc mdc P).
Definition RFC_C3_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur cid pos : Z)
W1 (regs1 : bvmap 5 word) mem1 md1 (r1 r2 r3 cur2 cur3 fattr fgen delay : Z) (T : Z) (P : list Z),
rfc_cx STK sp0 FP ly S own lyc Sc k regs Bb st dst N pdata nb cur cid pos T P ->
garr8 tfibsegs (mrestrict (w_H W) memc) pdata P ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W1 mem1 md1 k ->
hdr3 P cur nb r1 r2 r3 cur2 cur3 fattr fgen delay ->
C3_regs_at regs regs1 st dst N r1 r2 r3 cur3 ->
rfc_frame (mrestrict (w_H W1) mem1) (spZ regs) regs ->
rfc_memI (mrestrict (w_H W1) mem1) st dst pdata nb cur2 0 fattr fgen delay 0 0 ->
range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF dst 32 ->
rfc_kept B W memc W1 mem1 (spZ regs) Bb lyc Sc st dst -> same_io mdc md1 ->
SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 RFC_RD3) mem1 (seg_rom tfibsegs)) md1)
(rfc_post STK sp0 FP ly S W0 mem0 md0 own k regs Bb st dst N pdata nb cur lyc Sc W memc mdc P).
Definition RFC_C1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur cid pos : Z)
W1 (regs1 : bvmap 5 word) mem1 md1 (r1 cur1 fattr : Z) (T : Z) (P : list Z),
rfc_cx STK sp0 FP ly S own lyc Sc k regs Bb st dst N pdata nb cur cid pos T P ->
garr8 tfibsegs (mrestrict (w_H W) memc) pdata P ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W1 mem1 md1 k ->
hdr1 P cur nb r1 cur1 fattr ->
C1_regs_at regs regs1 st dst N r1 cur1 ->
rfc_frame (mrestrict (w_H W1) mem1) (spZ regs) regs ->
rfc_memI (mrestrict (w_H W1) mem1) st dst pdata nb cur 0 fattr 0 0 0 0 ->
range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF dst 32 ->
rfc_kept B W memc W1 mem1 (spZ regs) Bb lyc Sc st dst -> same_io mdc md1 ->
SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 RFC_RD1) mem1 (seg_rom tfibsegs)) md1)
(rfc_post STK sp0 FP ly S W0 mem0 md0 own k regs Bb st dst N pdata nb cur lyc Sc W memc mdc P).
Lemma rfc_frame_of_stackA : forall E m (regs : bvmap 5 word) cs lo hi wlo whi,
region_ok tfibsegs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = spZ regs ->
(forall j, (j < 12)%nat -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat (nth j rfc_saved 0)) 0))) cs) ->
(forall j, (j < 12)%nat -> ew E (Z.to_nat (nth j rfc_saved 0)) = getr regs (Z_to_bv 5 (nth j rfc_saved 0))) ->
rfc_frame m (spZ regs) regs.
Proof.
intros E m regs cs lo hi wlo whi HR Hsp Hcs Hval j r Hj.
assert (Hlt : (j < 12)%nat) by (destruct (Nat.lt_ge_cases j 12) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None rfc_saved j)) in Hj; [discriminate | cbn; lia]).
assert (Hr : nth j rfc_saved 0 = r) by (apply nth_error_nth; exact Hj).
replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia. change 8%nat with (N.to_nat 8).
apply (field_of_region E m 2 (spZ regs) cs lo hi wlo whi (-8 - 8 * Z.of_nat j) 8 (SOff (Z.to_nat (nth j rfc_saved 0)) 0) _ HR Hsp (Hcs j Hlt)).
- cbn [sv_denot]. rewrite Z.add_0_r, (Hval j Hlt), Hr, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRg. change (bv_modulus 64) with (2 ^ 64) in HRg. cbn. lia.
- cbn. lia.
Qed.
Lemma zero_of_region : forall E m n b cs lo hi wlo whi od len a w,
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CZero len)) cs -> od <= a - b -> a - b + Z.of_nat w <= od + len ->
val_mem tfibsegs m a w 0.
Proof.
intros E m n b cs lo hi wlo whi od len a w (_ & _ & _ & Hcs) Hn Hc Hlo Hhi k Hk.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck (a + Z.of_nat k - b - od) ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-.
replace (b + od + (a + Z.of_nat k - b - od)) with (a + Z.of_nat k) in Hb2 by lia. rewrite Hb2. f_equal. f_equal.
unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
Definition rd_cut (STK sp0 : Z) FP ly S W0 mem md own lyc Sc (W : world tfibsegs) mdc k (ssJ : sstate) (Eb : env) (Kb : nat)
(memT : word -> option byte) (st d n pdata nb cur o dz pc : Z) :=
fun (W2 : world tfibsegs) c2 => W2 = W /\ exists E2 regs2 mem2 md2 (r cur2 : Z),
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs)) md2 /\
st_ok tfibsegs E2 ssJ (mkst regs2 (Z_to_bv 64 pc) (mrestrict (w_H W) mem2) (seg_rom tfibsegs)) /\
(forall j, (j < Kb)%nat -> ew E2 j = ew Eb j) /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
getr regs2 10 = w64 r /\ getr regs2 11 = w64 cur2 /\
((r = 0 /\ cur + n <= nb /\ cur2 = cur + n /\
forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem2 (d + i) = aview tfibsegs (w_H W) memT (pdata + cur + i))
\/ (r = 2 ^ 64 - 1 /\ nb < cur + n /\ cur2 = nb /\
forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem2 (d + i) = aview tfibsegs (w_H W) memT (d + i))) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - 32 - ESTACK <= a < sp0 + o + 96) -> ~ (dz <= a < dz + 16) ->
~ (st + 16 <= a < st + 24) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_io mdc md2.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma rfc_entry_at : forall (pc : Z) (sr : list sv) (wd : Z) W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos racc cur,
AR tfibsegs B ly1 S1 W1 mem1 md1 ->
In (pdata, nb) (ablocks B ly1 S1) -> In (cid, pos) (frames S1) ->
spZ regs <= st -> st + 24 <= sp0 ->
frame_addr ly1 cid pos <= dst -> dst + 32 <= frame_addr ly1 cid pos + fs_frame_bytes cid ->
rboxed (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 ->
1 <= N <= 100000000 -> 0 < nb -> rfc_vals racc curv lpa nlp fattr fgen delay tidx cur nb -> 0 <= cur ->
astk_ok STK lya sp0 -> spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRFC_STK -> spZ regs <= sp0 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
I_regs_at regs regs1 st dst N racc ->
rfc_frame (mrestrict (w_H W1) mem1) (spZ regs) regs ->
rfc_memI (mrestrict (w_H W1) mem1) st dst pdata nb curv lpa fattr fgen delay nlp tidx ->
(wd = 16 \/ wd = 32) -> regs_ok (Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)) sr regs1 ->
st_ok tfibsegs (Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)) (mkSS pc sr (rfc_regions_d (YP09.mkRegion (Some 8%nat) 0 32 0 wd (YP09.mkChunk 0 (CVal 8 (SOff 35 0)) :: I_cfg_tail))) None (mkFacts I_facts [] []))
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 pc) mem1 (seg_rom tfibsegs))).
Proof.
intros pc sr wd W1 regs regs1 mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos racc cur
HAR Hpd Hfin Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV Hcur0 Hstk Hal16 Hwlo Hwhi Hpres HRP HFR HM Hwd HSR.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HV as (Hracc & Hcurv & Hlpa & Hnlp & Hfattr & Hfgen & Hdelay & Htidx).
pose proof HM as (Wp & Wn & Wc & Wl & Wz & Wfa & Wfg & Wde & Wnl & Wti).
pose proof HRP as (R2 & R3 & R4 & R8 & R18 & R19 & R25 & R22 & R9 & R20 & R23 & R24 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpd) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _ & HnbM). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pdata nb HAR Hpd) as Hph_img.
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]. unfold MALLOC_MAX in HnbM.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2. pose proof (fs_frame_bytes_nonneg cid) as HFB.
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (EX : forall j, ew E (32 + j) = nth j (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; apply EX).
assert (E2 : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E8 : ew E 8 = Z_to_bv 64 dst) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 N) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 st) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E25 : ew E 25 = Z_to_bv 64 racc) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 33%nat ltac:(lia)) as E33. pose proof (ES 34%nat ltac:(lia)) as E34. pose proof (ES 35%nat ltac:(lia)) as E35.
pose proof (ES 48%nat ltac:(lia)) as E48. pose proof (ES 49%nat ltac:(lia)) as E49. pose proof (ES 50%nat ltac:(lia)) as E50.
pose proof (ES 51%nat ltac:(lia)) as E51. pose proof (ES 52%nat ltac:(lia)) as E52.
cbn [Nat.sub nth I_extra map app rfc_saved] in E32, E33, E34, E35, E48, E49, E50, E51, E52.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold rfc_regions_d. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)) with E.
- exact HSR.
- destruct Hwd as [-> | ->]; vm_compute; reflexivity.
- unfold I_stack, got_region, bcell_region, I_st, st_region, I_dst, I_cfg_tail.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+   cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia. }
lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
let j := eval compute in (n - 36)%nat in let r := eval compute in (nth j rfc_saved 0) in
apply (chunk_ok_val tfibsegs E _ (spZ regs - 96) off 8 (SOff n 0) (bv_unsigned (ew E n)));
[ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; clear - HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
| cbn; lia
| replace (spZ regs - 96 + off) with (spZ regs - 8 - 8 * Z.of_nat j) by lia;
rewrite (ES n ltac:(lia)); cbn [Nat.sub nth I_extra map app rfc_saved]; exact (HFR j r eq_refl) ] end.
+ cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0x9df98) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0x9df98 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W1) mem1 _ _ Kgot).
+ cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa5ff8) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0xa5ff8 8 (SOff 22 0) SB);
[cbn [sv_denot]; rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W1) mem1 _ _ Kcell).
+   rewrite (VB 8%nat dst E8) by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable tfibsegs). apply (proj1 (HFpres (dst + o) ltac:(lia))). }
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]].
* apply (chunk_ok_val tfibsegs E _ dst 0 8 _ lpa); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Wl].
* apply (chunk_ok_zero tfibsegs). intros i Hi. specialize (Wz (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Wz by lia.
replace (dst + 8 + i) with (dst + 8 + i) by lia. rewrite Wz. f_equal. f_equal.
unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
* apply (chunk_ok_val tfibsegs E _ dst 16 4 _ fattr); [cbn [sv_denot]; rewrite E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wfa].
* apply (chunk_ok_val tfibsegs E _ dst 20 4 _ fgen); [cbn [sv_denot]; rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wfg].
* apply (chunk_ok_val tfibsegs E _ dst 24 2 _ delay); [cbn [sv_denot]; rewrite E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wde].
* apply (chunk_ok_val tfibsegs E _ dst 26 2 _ nlp); [cbn [sv_denot]; rewrite E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wnl].
* apply (chunk_ok_val tfibsegs E _ dst 28 1 _ tidx); [cbn [sv_denot]; rewrite E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wti].
+   rewrite (VB 19%nat st E19) by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia. }
constructor; [|constructor; [|constructor; [|constructor]]].
* apply (chunk_ok_val tfibsegs E _ st 0 8 _ pdata); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Wp].
* apply (chunk_ok_val tfibsegs E _ st 8 8 _ nb); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wn].
* apply (chunk_ok_val tfibsegs E _ st 16 8 _ curv); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wc].
- apply pairwise_disjoint_of_extents. unfold I_stack, got_region, bcell_region, I_st, st_region, I_dst, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 8%nat dst E8), (VB 19%nat st E19) by lia. cbn [base_val]. rewrite E2.
unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold rboxed in Hsd.
revert Hslo Hshi H47 Hceil Hwlo Hwhi C1 C3 HTS Has Hstk0 Hst1 Hst2 Hdst1 Hdst2 Hsd HFhi1 HFhi2 HFhi2_img. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok I_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E8, E18, E19, E22, E32, E33, E34, E48, E49, E50, E51, E52, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hwlo Hwhi Hal16 Hst1 Hst2 Hdst1 Hdst2 Hst8 Hdst8 HN Hcurv Hcur0 Hnb Hp16 Hp4096 Hpceil Hph Hph_img HnbM Hrq1 Hrq2 HFhi1 HFhi2 HFhi2_img C1 C3 HTS Has Hstk0 Hsp0al Hfattr Hfgen Hdelay Hnlp Htidx. clear. unfold off_img.
unfold SB. intros. repeat match goal with |- _ /\ _ => split end; try lia.
replace (spZ regs - 96) with (spZ regs + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
Qed.
Lemma rfc_I_entry : forall W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos racc cur,
AR tfibsegs B ly1 S1 W1 mem1 md1 ->
In (pdata, nb) (ablocks B ly1 S1) -> In (cid, pos) (frames S1) ->
spZ regs <= st -> st + 24 <= sp0 ->
frame_addr ly1 cid pos <= dst -> dst + 32 <= frame_addr ly1 cid pos + fs_frame_bytes cid ->
rboxed (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 ->
1 <= N <= 100000000 -> 0 < nb -> rfc_vals racc curv lpa nlp fattr fgen delay tidx cur nb -> 0 <= cur ->
astk_ok STK lya sp0 -> spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRFC_STK -> spZ regs <= sp0 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
I_regs_at regs regs1 st dst N racc ->
rfc_frame (mrestrict (w_H W1) mem1) (spZ regs) regs ->
rfc_memI (mrestrict (w_H W1) mem1) st dst pdata nb curv lpa fattr fgen delay nlp tidx ->
st_ok tfibsegs (Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)) ss_I_c
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 RFC_I) mem1 (seg_rom tfibsegs))).
Proof.
intros W1 regs regs1 mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos racc cur
HAR Hpd Hfin Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV Hcur0 Hstk Hal16 Hwlo Hwhi Hpres HRP HFR HM.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HV as (Hracc & Hcurv & Hlpa & Hnlp & Hfattr & Hfgen & Hdelay & Htidx).
pose proof HM as (Wp & Wn & Wc & Wl & Wz & Wfa & Wfg & Wde & Wnl & Wti).
pose proof HRP as (R2 & R3 & R4 & R8 & R18 & R19 & R25 & R22 & R9 & R20 & R23 & R24 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpd) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _ & HnbM). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pdata nb HAR Hpd) as Hph_img.
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]. unfold MALLOC_MAX in HnbM.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2. pose proof (fs_frame_bytes_nonneg cid) as HFB.
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
change ss_I_c with ss_I. unfold ss_I. change rfc_regions with (rfc_regions_d (YP09.mkRegion (Some 8%nat) 0 32 0 16 (YP09.mkChunk 0 (CVal 8 (SOff 35 0)) :: I_cfg_tail))).
apply (rfc_entry_at RFC_I I_regs 16 W1 regs regs1 mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos racc cur
HAR Hpd Hfin Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV Hcur0 Hstk Hal16 Hwlo Hwhi Hpres HRP HFR HM (or_introl eq_refl)).
set (E := Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E19 : ew E 19 = Z_to_bv 64 st) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
unfold I_regs.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite R9. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 19 st 16 E19) by lia. reflexivity.
+ rewrite R20. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 19 st 8 E19) by lia. reflexivity.
+ rewrite R23. symmetry. unfold I_sh, IBx. rewrite (denot_shx E 19 22 16 st SB E19 E22) by (unfold SB; lia). reflexivity.
+ rewrite R24. symmetry. unfold I_sh, IBx. rewrite (denot_shx E 19 22 8 st SB E19 E22) by (unfold SB; lia). reflexivity.
Qed.
Lemma rfc_J_entry : forall W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos racc cur fb,
AR tfibsegs B ly1 S1 W1 mem1 md1 ->
In (pdata, nb) (ablocks B ly1 S1) -> In (cid, pos) (frames S1) ->
spZ regs <= st -> st + 24 <= sp0 ->
frame_addr ly1 cid pos <= dst -> dst + 32 <= frame_addr ly1 cid pos + fs_frame_bytes cid ->
rboxed (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 ->
1 <= N <= 100000000 -> 0 < nb -> rfc_vals racc curv lpa nlp fattr fgen delay tidx cur nb -> 0 <= cur ->
astk_ok STK lya sp0 -> spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRFC_STK -> spZ regs <= sp0 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
J_regs_at regs regs1 st dst N racc fb ->
rfc_frame (mrestrict (w_H W1) mem1) (spZ regs) regs ->
rfc_memI (mrestrict (w_H W1) mem1) st dst pdata nb curv lpa fattr fgen delay nlp tidx ->
st_ok tfibsegs (Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)) ss_J_c
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 RFC_J) mem1 (seg_rom tfibsegs))).
Proof.
intros W1 regs regs1 mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos racc cur fb
HAR Hpd Hfin Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV Hcur0 Hstk Hal16 Hwlo Hwhi Hpres HRJ HFR HM.
destruct HRJ as (HRI & R21 & R10).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HV as (Hracc & Hcurv & Hlpa & Hnlp & Hfattr & Hfgen & Hdelay & Htidx).
pose proof HM as (Wp & Wn & Wc & Wl & Wz & Wfa & Wfg & Wde & Wnl & Wti).
pose proof HRI as (R2 & R3 & R4 & R8 & R18 & R19 & R25 & R22 & R9 & R20 & R23 & R24 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpd) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _ & HnbM). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pdata nb HAR Hpd) as Hph_img.
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]. unfold MALLOC_MAX in HnbM.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2. pose proof (fs_frame_bytes_nonneg cid) as HFB.
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
change ss_J_c with ss_J. unfold ss_J. change rfc_regions with (rfc_regions_d (YP09.mkRegion (Some 8%nat) 0 32 0 16 (YP09.mkChunk 0 (CVal 8 (SOff 35 0)) :: I_cfg_tail))).
apply (rfc_entry_at RFC_J J_regs 16 W1 regs regs1 mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos racc cur
HAR Hpd Hfin Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV Hcur0 Hstk Hal16 Hwlo Hwhi Hpres HRI HFR HM (or_introl eq_refl)).
set (E := Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E8 : ew E 8 = Z_to_bv 64 dst) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E19 : ew E 19 = Z_to_bv 64 st) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
unfold J_regs. apply regs_ok_pin; [| intros X; discriminate X |].
2: { rewrite R21. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 8 dst 26 E8) by lia. reflexivity. }
unfold I_regs.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite R9. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 19 st 16 E19) by lia. reflexivity.
+ rewrite R20. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 19 st 8 E19) by lia. reflexivity.
+ rewrite R23. symmetry. unfold I_sh, IBx. rewrite (denot_shx E 19 22 16 st SB E19 E22) by (unfold SB; lia). reflexivity.
+ rewrite R24. symmetry. unfold I_sh, IBx. rewrite (denot_shx E 19 22 8 st SB E19 E22) by (unfold SB; lia). reflexivity.
Qed.
Lemma rfc_C3_entry : forall W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos cur r1 r2 r3 cur3,
AR tfibsegs B ly1 S1 W1 mem1 md1 ->
In (pdata, nb) (ablocks B ly1 S1) -> In (cid, pos) (frames S1) ->
spZ regs <= st -> st + 24 <= sp0 ->
frame_addr ly1 cid pos <= dst -> dst + 32 <= frame_addr ly1 cid pos + fs_frame_bytes cid ->
rboxed (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 ->
1 <= N <= 100000000 -> 0 < nb -> rfc_vals (bv_unsigned (getr regs1 25)) curv lpa nlp fattr fgen delay tidx cur nb -> 0 <= cur ->
astk_ok STK lya sp0 -> spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRFC_STK -> spZ regs <= sp0 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
C3_regs_at regs regs1 st dst N r1 r2 r3 cur3 ->
rfc_frame (mrestrict (w_H W1) mem1) (spZ regs) regs ->
rfc_memI (mrestrict (w_H W1) mem1) st dst pdata nb curv lpa fattr fgen delay nlp tidx ->
st_ok tfibsegs (Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)) ss_C3_c
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 RFC_RD3) mem1 (seg_rom tfibsegs))).
Proof.
intros W1 regs regs1 mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos cur r1 r2 r3 cur3
HAR Hpd Hfin Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV Hcur0 Hstk Hal16 Hwlo Hwhi Hpres HRC HFR HM.
destruct HRC as (HRI & R10 & R14 & R15 & R16 & R17 & R13).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HV as (Hracc & Hcurv & Hlpa & Hnlp & Hfattr & Hfgen & Hdelay & Htidx).
pose proof HM as (Wp & Wn & Wc & Wl & Wz & Wfa & Wfg & Wde & Wnl & Wti).
pose proof HRI as (R2 & R3 & R4 & R8 & R18 & R19 & R25 & R22 & R9 & R20 & R23 & R24 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpd) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _ & HnbM). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pdata nb HAR Hpd) as Hph_img.
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]. unfold MALLOC_MAX in HnbM.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2. pose proof (fs_frame_bytes_nonneg cid) as HFB.
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
change ss_C3_c with ss_C3. unfold ss_C3, C3_dst.
apply (rfc_entry_at RFC_RD3 C3_regs 32 W1 regs regs1 mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos (bv_unsigned (getr regs1 25)) cur
HAR Hpd Hfin Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV Hcur0 Hstk Hal16 Hwlo Hwhi Hpres HRI HFR HM (or_intror eq_refl)).
set (E := Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E8 : ew E 8 = Z_to_bv 64 dst) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E19 : ew E 19 = Z_to_bv 64 st) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
unfold C3_regs. apply regs_ok_pin; [| intros X; discriminate X |].
2: { rewrite R14, (denot_srl3 E 8 16 dst E8) by lia. reflexivity. }
apply regs_ok_pin; [| intros X; discriminate X |].
2: { rewrite R10. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 8 dst 16 E8) by lia. reflexivity. }
unfold I_regs.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite R9. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 19 st 16 E19) by lia. reflexivity.
+ rewrite R20. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 19 st 8 E19) by lia. reflexivity.
+ rewrite R23. symmetry. unfold I_sh, IBx. rewrite (denot_shx E 19 22 16 st SB E19 E22) by (unfold SB; lia). reflexivity.
+ rewrite R24. symmetry. unfold I_sh, IBx. rewrite (denot_shx E 19 22 8 st SB E19 E22) by (unfold SB; lia). reflexivity.
Qed.
Lemma rfc_C1_entry : forall W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos cur r1 cur1,
AR tfibsegs B ly1 S1 W1 mem1 md1 ->
In (pdata, nb) (ablocks B ly1 S1) -> In (cid, pos) (frames S1) ->
spZ regs <= st -> st + 24 <= sp0 ->
frame_addr ly1 cid pos <= dst -> dst + 32 <= frame_addr ly1 cid pos + fs_frame_bytes cid ->
rboxed (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 ->
1 <= N <= 100000000 -> 0 < nb -> rfc_vals (bv_unsigned (getr regs1 25)) curv lpa nlp fattr fgen delay tidx cur nb -> 0 <= cur ->
astk_ok STK lya sp0 -> spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRFC_STK -> spZ regs <= sp0 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
C1_regs_at regs regs1 st dst N r1 cur1 ->
rfc_frame (mrestrict (w_H W1) mem1) (spZ regs) regs ->
rfc_memI (mrestrict (w_H W1) mem1) st dst pdata nb curv lpa fattr fgen delay nlp tidx ->
st_ok tfibsegs (Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)) ss_C1_c
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 RFC_RD1) mem1 (seg_rom tfibsegs))).
Proof.
intros W1 regs regs1 mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos cur r1 cur1
HAR Hpd Hfin Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV Hcur0 Hstk Hal16 Hwlo Hwhi Hpres HRC HFR HM.
destruct HRC as (HRI & R10 & R14 & R15 & R13).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HV as (Hracc & Hcurv & Hlpa & Hnlp & Hfattr & Hfgen & Hdelay & Htidx).
pose proof HM as (Wp & Wn & Wc & Wl & Wz & Wfa & Wfg & Wde & Wnl & Wti).
pose proof HRI as (R2 & R3 & R4 & R8 & R18 & R19 & R25 & R22 & R9 & R20 & R23 & R24 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpd) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _ & HnbM). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pdata nb HAR Hpd) as Hph_img.
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]. unfold MALLOC_MAX in HnbM.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2. pose proof (fs_frame_bytes_nonneg cid) as HFB.
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
change ss_C1_c with ss_C1. unfold ss_C1, C3_dst.
apply (rfc_entry_at RFC_RD1 C3_regs 32 W1 regs regs1 mem1 ly1 S1 md1 lya STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos (bv_unsigned (getr regs1 25)) cur
HAR Hpd Hfin Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV Hcur0 Hstk Hal16 Hwlo Hwhi Hpres HRI HFR HM (or_intror eq_refl)).
set (E := Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E8 : ew E 8 = Z_to_bv 64 dst) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E19 : ew E 19 = Z_to_bv 64 st) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
unfold C3_regs. apply regs_ok_pin; [| intros X; discriminate X |].
2: { rewrite R14, (denot_srl3 E 8 16 dst E8) by lia. reflexivity. }
apply regs_ok_pin; [| intros X; discriminate X |].
2: { rewrite R10. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 8 dst 16 E8) by lia. reflexivity. }
unfold I_regs.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite R9. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 19 st 16 E19) by lia. reflexivity.
+ rewrite R20. symmetry. rewrite denot_lit_U. unfold w64. f_equal. rewrite (U_atom_off E 19 st 8 E19) by lia. reflexivity.
+ rewrite R23. symmetry. unfold I_sh, IBx. rewrite (denot_shx E 19 22 16 st SB E19 E22) by (unfold SB; lia). reflexivity.
+ rewrite R24. symmetry. unfold I_sh, IBx. rewrite (denot_shx E 19 22 8 st SB E19 E22) by (unfold SB; lia). reflexivity.
Qed.
End e.
End d.
Ltac reseatX HS HJ2 HP2 keep AG AGX kept_tac :=
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 (SOff 32 0) [] ss) end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
lazymatch type of AGX with forall j, (j < ?KX)%nat -> ew _ j = ew ?Er j =>
let AGX2 := fresh "AGX" in
assert (AGX2 : forall j, (j < KX)%nat -> ew Ev j = ew Er j)
by (intros jj Hjj; rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
first [reflexivity | rewrite AGX by exact Hjj; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; reflexivity]);
clear AGX; rename AGX2 into AGX end;
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG end end.
Ltac rebaseJ HS HS3 AGX3 AG :=
clear HS; rewrite <- restrict_mkst_fx in HS3; rename HS3 into HS;
lazymatch type of AGX3 with forall j, _ -> _ = ew ?Eb j =>
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let AG2 := fresh "AG" in
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n) by (intros nn Hnn; rewrite AGX3 by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| Eb => let H2 := fresh H in assert (H2 : ew Ev n = v) by (rewrite AGX3 by lia; exact H); clear H; rename H2 into H
end end;
clear AG; rename AG2 into AG end end end.
