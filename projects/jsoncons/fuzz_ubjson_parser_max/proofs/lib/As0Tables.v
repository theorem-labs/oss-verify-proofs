(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__As0Tables () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1true"; "2and"; "2eq"; "2or"; "3map"; "4Z"; "5app_mem"; "5chunks_per_map"; "5class_id"; "5class_ok"]; ["5class_size"; "5from_primary"; "5in_mem"; "5kHighMemBeg"; "5kHighMemEnd"; "5max_cached"; "5needed"; "5round_up"; "5rz_log"; "5rz_size"; "5sec_map_size"; "5shad"; "5ziota"; "5zrange"; "6In"; "6forallb"]; ["7add"; "7le"; "7lt"; "7modulo"; "7of_nat"; "7pow"; "7sub"; "0a"; "0i"; "0k"; "0lo"; "0n"; "0s"; "0x"]]).
Module AsanTab.
Definition SB : Z := 0x7fff8000.
Definition shad (a : Z) : Z := a / 8 + SB.
Definition BIG_LO : Z := 0x7fff7000.
Definition BIG_HI : Z := 0x10007fff8000.
Definition kLowMemEnd : Z := 0x7fff7fff.
Definition kHighMemBeg : Z := 0x10007fff8000.
Definition kHighMemEnd : Z := 2 ^ 47 - 1.
Definition in_mem (a : Z) : bool := (a <=? kLowMemEnd) || ((kHighMemBeg <=? a) && (a <=? kHighMemEnd)).
Definition app_mem (a n : Z) : Prop := a + n <= BIG_LO \/ BIG_HI <= a.
Lemma kHighMemBeg_eq : ltac2:(TCodec.tc2 tcn__As0Tables ":'8';&C&Q0&K&D%211+1%5221%93871").
Proof. reflexivity. Qed.
Lemma in_mem_app : ltac2:(TCodec.tc2 tcn__As0Tables "Q7';&Q1zr3%3221&Q2%1243&Q0r5r4%3221&Q5+2+Q?%3221%>251&<r6%221:'7%C2B<%@2=4%3221'8'0&Br8%D21:%311(6%73621p091p0>1p0B1p0L1p0O1pRBQ41pRHQ51pR@Q61").
Proof.
intros a n i Ha Hn Htop [H|H] Hi; unfold in_mem, kLowMemEnd, kHighMemBeg, kHighMemEnd, BIG_LO, BIG_HI in *;
apply orb_true_iff; [left|right]; [apply Z.leb_le; lia | apply andb_true_iff; split; apply Z.leb_le; lia].
Qed.
Definition rz_log (n : Z) : Z :=
if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := 16 * 2 ^ rz_log n.
Definition round_up (x m : Z) : Z := (x + m - 1) / m * m.
Definition needed0 (n : Z) (al16 : bool) : Z := round_up (Z.max n 8) 8 + rz_size n + (if al16 then 16 else 0).
Definition kMaxSize : Z := 0x10000.
Definition from_primary (n : Z) (al16 : bool) : bool := needed0 n al16 <=? kMaxSize.
Definition needed (n : Z) (al16 : bool) : Z := if from_primary n al16 then needed0 n al16 else needed0 n al16 + rz_size n.
Definition user_off (n : Z) : Z := rz_size n.
Lemma rz_log_range : ltac2:(TCodec.tc2 tcn__As0Tables "<';'7&Q1z&Hr1%211%5241+7%7231%9231pRH;1").
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.
Lemma rz_size_values : ltac2:(TCodec.tc2 tcn__As0Tables "J';&N&Ir1%211(1+@+Q0+R0+T0+X0+`0+QP0+RP0(5%11?%;3@31%<3A51%=3B71%>3C91%?3D;1%@3E=1%A3F?1%B3GA1%G3HD1pRHI1").
Proof. intros n. unfold rz_size, rz_log. repeat (destruct (_ <=? _)); cbn; tauto. Qed.
Definition kNumClasses : Z := 32.
Definition class_size (c : Z) : Z :=
if c <=? 16 then 32 * c
else let t := Z.shiftl 512 ((c - 16) / 2) in t + (if Z.odd (c - 16) then t / 2 else 0).
Definition class_id (s : Z) : Z :=
if s <=? 512 then (s + 31) / 32
else let l := Z.log2 s in
let hbit := (Z.shiftr s (l - 1)) mod 2 in
let lbits := s mod 2 ^ (l - 1) in
2 * l - 2 + hbit + (if lbits =? 0 then 0 else 1).
Definition max_cached (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / class_size c)).
Definition kRegionSize : Z := 2 ^ 32.
Definition kFreeArrayOffset : Z := 0xE0000000.
Definition kFreeArraySize : Z := 2 ^ 29.
Definition kUserMapSize : Z := 2 ^ 18.
Definition kSpaceSize : Z := 2 ^ 37.
Definition kSpaceReserve : Z := 0x2000011000.
Definition region_beg (space_beg c : Z) : Z := space_beg + c * kRegionSize.
Definition chunk_addr (space_beg c i : Z) : Z := region_beg space_beg c + i * class_size c.
Definition compact (space_beg c p : Z) : Z := (p - region_beg space_beg c) / 16.
Definition rinfo (space_beg c : Z) : Z := space_beg + kSpaceSize + 128 * c.
Definition chunks_per_map (c : Z) : Z := kUserMapSize / class_size c.
Definition sec_map_size (needed_sz : Z) : Z := round_up needed_sz 4096 + 4096.
Definition sec_user (map_beg n : Z) : Z := map_beg + 4096 + rz_size n.
Definition kQuarantineMax : Z := 2 ^ 28.
Definition kQuarantineMin : Z := 0xE666661.
Definition kLocalQuarantineMax : Z := 2 ^ 20.
Definition kBatchSlots : Z := 1021.
Definition kBatchBytes : Z := 8192.
Definition fs_log : Z := 20.
Definition fs_frame_bytes (k : Z) : Z := 64 * 2 ^ k.
Definition fs_nframes (k : Z) : Z := 2 ^ (fs_log - 6 - k).
Definition fs_flags_off (k : Z) : Z := 4096 + (2 ^ (fs_log - 5) - 2 ^ (fs_log - 5 - k)).
Definition fs_frame (fs k i : Z) : Z := fs + 4096 + 2 ^ (fs_log - 5) + k * 2 ^ fs_log + i * fs_frame_bytes k.
Definition fs_size : Z := 0xb09000.
Definition kDepotL2Nodes : Z := 2 ^ 16.
Definition kStoreBlockFrames : Z := 2 ^ 20.
Definition kMaxTraceDepth : Z := 30.
Fixpoint ziota (lo : Z) (k : nat) : list Z := match k with O => [] | S k' => lo :: ziota (lo + 1) k' end.
Definition zrange (lo n : Z) : list Z := ziota lo (Z.to_nat n).
Lemma in_ziota : ltac2:(TCodec.tc2 tcn__As0Tables "H'4';'7&Q1r2r1%3221&Q2&Q0&Q4r3%211%4281%6281%<281&N&Lr4%2281%43B?1p061pRLD1pRFE1pRDG1").
Proof. induction k as [|k IH]; intros lo x H; [lia|]. cbn. destruct (Z.eq_dec lo x); [left; assumption | right; apply IH; lia]. Qed.
Lemma class_size_table : ltac2:(TCodec.tc2 tcn__As0Tables "R;'8'3';%211&:&@&M+1+N%3221%648851(1+Q0+R0+S0+T0+U0+V0+W0+X0+Y0+Z0+[0+\0+]0+^0+_0+`0+h0+QP0+Q`0+RP0+SP0+TP0+VP0+XP0+\P0+`P0+hP0+QPP0+Q`P0+RPP0(5%11Q9%Q13Q:31%Q23Q;51%Q33Q<71%Q43Q=91%Q53Q>;1%Q63Q?=1%Q73Q@?1%Q83QAA1%Q93QBC1%Q:3QCE1%Q;3QDG1%Q<3QEI1%Q=3QFK1%Q>3QGM1%Q?3QHO1%Q@3QIQ11%QA3QJQ31%QB3QKQ51%QC3QLQ71%QD3QMQ91%QE3QNQ;1%QF3QOQ=1%QG3R0Q?1%QH3R1QA1%QI3R2QC1%QJ3R3QE1%QK3R4QG1%QL3R5QI1%QM3R6QK1%QN3R7QM1%R:3R7R01").
Proof. vm_compute. reflexivity. Qed.
Lemma max_cached_table : ltac2:(TCodec.tc2 tcn__As0Tables "QD'8'3';%211&:&E&M+1+N%3221%648851(1+@+<+:+8+6+4+2(5%11B%:3C31%;3D41%<3E51%=3F61%>3G71%?3H81%@3I91%A3J:1%B3K;1%C3L<1%D3M=1%E3N>1%F3O?1%G3Q0@1%H3Q1B1%I3Q2C1%J3Q3D1%K3Q4E1%L3Q5F1%M3Q6G1%N3Q7I1%O3Q8J1%Q03Q9L1%Q13Q:M1%Q23Q;O1%Q33Q<Q11%Q43Q=Q31%Q53Q>Q41%Q63Q?Q51%Q73Q@Q61%QC3Q@Q91").
Proof. vm_compute. reflexivity. Qed.
Lemma chunks_per_map_table : ltac2:(TCodec.tc2 tcn__As0Tables "QK'8'3';%211&:&=(1+1+2+3+6+7+8+@+C+E+G+H+N(5%11B%?3C31%@3D51%A3E71%B3F91%C3G;1%D3H=1%E3I?1%F3JA1%G3KC1%H3LE1%I3MG1%J3NI1%M4OOL1+XP0+TP0+Re:+QZE+QTB+QP0+`0+U:+RE+Q:+Q0+4%Q83Q<1J%Q93Q=31%Q:3Q>51%Q;3Q?71%Q<3Q@91%Q=3QA;1%Q>3QB=1%Q?3QC?1%Q@3QDA1%QA3QEC1%QB3QFE1%QC3QGG1%QJ3QGI1").
Proof. vm_compute. reflexivity. Qed.
Definition class_ok (s : Z) : bool :=
let c := class_id s in (1 <=? c) && (c <=? 30) && (s <=? class_size c) && ((c =? 1) || (class_size (c - 1) <? s)).
Lemma class_id_ok_all : ltac2:(TCodec.tc2 tcn__As0Tables "<'8'0&O';&?&M+1+RPP0%3221%73651(6%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma class_id_ok : ltac2:(TCodec.tc2 tcn__As0Tables "Q0';'7&Q1+1r1%3221+RPP0%5231%7231&>r2%211%:291+N%<231%>231&@%116%@281'9'8%13E:B&Q2&Q6%12=E%911%421@%8261%K2:1%L2>1p0F1pRJO1").
Proof.
intros s Hs.
assert (Hin : In s (zrange 1 65536)).
{ unfold zrange. apply in_ziota. lia. }
pose proof class_id_ok_all as H. rewrite forallb_forall in H. specialize (H s Hin). unfold class_ok in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
apply orb_prop in H4. destruct H4 as [H4|H4]; [apply Z.eqb_eq in H4 | apply Z.ltb_lt in H4]; lia.
Qed.
Lemma examples : ltac2:(TCodec.tc2 tcn__As0Tables "QM'7'8'0&A+RPP0(2%3221%63512';&J&F%1276%311+RXP0%=3621&>+3%721<%311+1%C3<21+R0%<21A%811%G3@18+T@(6%A221%=11+7%M3F21+S4%F21K%B11+6%Q23K21+o8%K21Q0%G11+C%Q73Q021+Tl7%Q021Q5%L11+G%Q<3Q521+XP0%Q011+H%Q@3Q921+RTP0%QB3Q;Q81%QD231%QE281%QF2>1%QG2D1%QH2J1%QI2Q11%QJ2Q61%QK2Q=1%QL2QE1").
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma round_up_8_spec : ltac2:(TCodec.tc2 tcn__As0Tables "G';&Q1zr1%3221'7r2&G+8%2231%9241&Q2&Q0%1275%3251%:251'8&Q3%129:%33C1A%?251p0A1pRLF1").
Proof. intros x Hx. unfold round_up. pose proof (Z.div_mod (x + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 8 - 1) 8 ltac:(lia)). split; [nia|]. apply Z.mod_mul. lia. Qed.
End AsanTab.
