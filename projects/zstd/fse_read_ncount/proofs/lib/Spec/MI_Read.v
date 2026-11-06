(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith.
Import ListNotations.
Local Open Scope Z_scope.
Lemma rd8_known {R} st q v (k : Z -> M R) :
cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.
Lemma known_at st rid o v rid' o' :
known st (rid, o) v -> o' = o -> rid' = rid -> cell_read (get_shadow st rid') o' = Known v.
Proof. intros H -> ->. exact H. Qed.
Lemma rd8_ftree {R} L st q (k : Z -> M R) Post :
(forall v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) ->
(forall v, 0 <= v < 256 -> ftree L (k v) Post) ->
ftree L (rd8 st q k) Post.
Proof.
intros Hk H. unfold rd8. destruct (cell_read _ _) as [v|h] eqn:E.
- apply H. apply Hk. reflexivity.
- cbn [ftree]. intros v Hv. unfold peek_answer_ok.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>29924571252.1430054731589.1444956394824.1400000:00;00?S2Hv2H12H0FS2Hv".
destruct (Z.leb_spec 0 v), (Z.ltb_spec v 256); cbn [andb]; try lia. apply H. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rd16_ftree {R} L st q (k : Z -> M R) Post :
(forall q' v, cell_read (get_shadow st (fst q')) (snd q') = Known v -> 0 <= v < 256) ->
(forall v, 0 <= v < 65536 -> ftree L (k v) Post) ->
ftree L (rd16 st q k) Post.
Proof.
intros Hk H. unfold rd16. apply rd8_ftree; [apply Hk|]. intros b0 H0. apply rd8_ftree; [apply Hk|]. intros b1 H1. apply H. Local Ltac2 Set LiaHints.tbl := fun () => "0010>49944219732.12000007S2H02H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma known_byte st rid o v :
(forall sh o' v' t, s_shadow st !! rid = Some sh -> r_cells sh !! o' = Some (v', t) -> 0 <= v' < 256) ->
cell_read (get_shadow st rid) o = Known v -> 0 <= v < 256.
Proof.
intros Hc H. unfold cell_read, get_shadow in H. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn [default id] in H.
- destruct (r_cells sh !! o) as [[v' t]|] eqn:E2.
+ match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. subst. eapply Hc; eauto.
+ match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. Local Ltac2 Set LiaHints.tbl := fun () => "0020>57019999624.1057019999624.8 000001002SS".
lia.
- rewrite !lookup_empty in H. cbn in H. inversion H. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_255 x : 0 <= x -> Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). Local Ltac2 Set LiaHints.tbl := fun () => "0010=63374621462.2000001S".
rewrite Z.land_ones by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma byte_of_0 x : 0 <= x -> byte_of x 0 = x mod 256.
Proof. intros. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r. apply land_255. Local Ltac2 Set LiaHints.tbl := fun () => "0010=56087383078.2000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma byte_of_1 x : 0 <= x -> byte_of x 1 = (x / 256) mod 256.
Proof. intros. unfold byte_of. Local Ltac2 Set LiaHints.tbl := fun () => "0040=18435116950.242924417835.256087383078.263374621462.2000001002005006SSS1HS".
replace (8 * 1) with 8 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply land_255. apply Z.div_pos; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma byte_of_2 x : 0 <= x -> byte_of x 2 = (x / 65536) mod 256.
Proof. intros. unfold byte_of. Local Ltac2 Set LiaHints.tbl := fun () => "0040=18930958230.250115332763.256087383078.265504523926.2000001002005006SSS1HS".
replace (8 * 2) with 16 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. apply land_255. apply Z.div_pos; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma byte_of_3 x : 0 <= x -> byte_of x 3 = (x / 16777216) mod 256.
Proof. intros. unfold byte_of. Local Ltac2 Set LiaHints.tbl := fun () => "0040=18930958230.238571587787.241885266454.256087383078.2000001002003006SSSS1H".
replace (8 * 3) with 24 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. apply land_255. apply Z.div_pos; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma u16_bytes q : 0 <= q < 2^16 -> byte_of q 0 + 256 * byte_of q 1 = q.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "0050=18435116950.239172643473.26219439143.3 7111344844.2 7244995288.2 00000100400800900<SS1HS2H0SS1H".
rewrite byte_of_0, byte_of_1 by lia. rewrite (Z.mod_small (q / 256)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). pose proof (Z.div_mod q 256 ltac:(lia)). lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma u32_bytes r : 0 <= r < 2^32 ->
byte_of r 0 + 256 * byte_of r 1 + 65536 * byte_of r 2 + 16777216 * byte_of r 3 = r.
Proof.
intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0=18433110315.518433110700.418926546033.518928632107.519497488098.546654879274.55361208676.2 5367591897.5 7109214071.3 7109214198.4 7111344844.2 00000100200300400>00A00D00G00H00I00JSSSSS2E12E22E3S1HS1HS1HSSS".
rewrite byte_of_0, byte_of_1, byte_of_2, byte_of_3 by lia.
pose proof (Z.div_mod r 256 ltac:(lia)) as E1.
pose proof (Z.div_mod (r / 256) 256 ltac:(lia)) as E2. rewrite (Z.div_div r 256 256) in E2 by lia. change (256 * 256) with 65536 in E2.
pose proof (Z.div_mod (r / 65536) 256 ltac:(lia)) as E3. rewrite (Z.div_div r 65536 256) in E3 by lia. change (65536 * 256) with 16777216 in E3.
rewrite (Z.mod_small (r / 16777216)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land31_idx i r : 0 <= i <= 31 -> 0 <= r -> Z.land (i + 32 * r) 31 = i.
Proof.
intros. change 31 with (Z.ones 5). Local Ltac2 Set LiaHints.tbl := fun () => "0030=29317564158.453973182066.463045830487.4000001002005SSS1H".
rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
replace (i + 32 * r) with (i + r * 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma shiftr5_res i r : 0 <= i <= 31 -> 0 <= r -> Z.shiftr (i + 32 * r) 5 = r.
Proof.
intros. Local Ltac2 Set LiaHints.tbl := fun () => "0050=29317564158.446609796340.449465631226.455397792577.463045830487.4000001002003004007SSSSS1H".
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
replace (i + 32 * r) with (r * 32 + i) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma area_of_mslot a k : snd a mod PGSZ = 0 -> 0 <= k < NSLOTS -> area_of (mslot a k) = a.
Proof.
intros Ha Hk. unfold area_of, mslot, aadd, AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. destruct a as [r o]; cbn in *. f_equal.
rewrite <- Zplus_mod_idemp_l, Ha. cbn [Z.add]. Local Ltac2 Set LiaHints.tbl := fun () => "0020=67542738194.59531840612.5 000004005S2HkS".
rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
