(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PlacementSearch.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanCeil () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanCeil."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1prod"; "1true"; "2eq"; "2iff"; "3lt"; "4firstn"; "4nth"; "4repeat"; "4skipn"]; ["5Z"; "6valid_sp"; "7at_random_bytes"; "8ProcInput"; "8VmMaps"; "8alloc_top"; "8init_model"; "8m_vmmaps"; "8mkVmMapsFull"; "8page_round_up_Z"; "8page_size"; "8vm_init_sp"; "9mmap_anon_b"; "9mmap_flags_core"; "9mmap_off_aligned_b"; ":w_is0"]; [";alloc_ceiling"; ";bottomup_floor"; ";hint_placement_ok_b"; ";init_sp_ok"; ";placement_ok"; ";placement_ok_b"; "<le"; "<lt"; "<modulo"; "<testbit"; "0aZ"; "0addr"; "0b"; "0brk0"; "0c"; "0d"]; ["0flags"; "0h"; "0h'"; "0i"; "0inp"; "0l"; "0lim"; "0m"; "0mb"; "0mbase"; "0nZ"; "0na"; "0r"; "0reserved"; "0sb"; "0sp"]; ["=Z_to_bv"; "=bv"; "0z"]]).
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : ltac2:(TCodec.tc2 tcn__AsanCeil "5'9'@&Q0+SoomohPPP0%43321").
Proof. reflexivity. Qed.
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : ltac2:(TCodec.tc2 tcn__AsanCeil "5'9'@&Q1+QZeZeZe\P0%43321").
Proof. reflexivity. Qed.
Definition placement_ok (h : VmMaps) (aZ nZ : Z) : Prop :=
bottomup_floor <= aZ
\/ no_higher_fit (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h)).
Definition placement_ok_b (h : VmMaps) (aZ nZ : Z) : bool :=
(bottomup_floor <=? aZ)%Z
|| negb (higher_fit_b (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h))).
Lemma placement_ok_b_iff : ltac2:(TCodec.tc2 tcn__AsanCeil "Q1'D'@&Q6zr2%3221&Q7%1243'9&Q8r4&J%3221%53<1:&:'0&Q5r7r6r5%43321(8%>3721&Q4%13765%;231p0=1p0>1p0E1p0H1pSFM1pRFN1pS4Q01").
Proof.
intros h aZ nZ HaPos HnPos HaAl HnAl. unfold placement_ok_b, placement_ok.
pose proof (bv_unsigned_in_range 64 (vm_mmap_base h)) as [_ Hbase].
assert (Hb : bv_unsigned (vm_mmap_base h) < two_pow_64) by (unfold two_pow_64; exact Hbase).
rewrite orb_true_iff, Z.leb_le, negb_true_iff.
rewrite (no_higher_fit_iff _ _ _ _ HaPos HnPos HaAl HnAl Hb). reflexivity.
Qed.
Lemma placement_ok_b_of_floor : ltac2:(TCodec.tc2 tcn__AsanCeil "B'D'@&Q6&Q1r2%3221'9'0&Q5r4r3%33217(8%73621p091pSF>1pRF?1pS4A1").
Proof. intros h aZ nZ H. unfold placement_ok_b. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.
Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
if w_is0 addr then placement_ok_b h aZ nZ else true.
Lemma hint_placement_ok_b_of_floor : ltac2:(TCodec.tc2 tcn__AsanCeil "G'R1yR0%211'D'@&Q6&Q1r2%3221'9'0&Q2r5r4r3%443218(8%83721p0:1pSF?1pRF@1pS4B1pRHD1").
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. destruct (w_is0 addr); [now apply placement_ok_b_of_floor|reflexivity]. Qed.
Lemma hint_placement_ok_b_nonnull : ltac2:(TCodec.tc2 tcn__AsanCeil "H'R1yR0%211'D'@'9'0&Or4%211(2%63521&Q2r5r3r2%443821(8%=3<21p081pSF@1pRFA1pS4C1pRHE1").
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. now rewrite H. Qed.
Definition placement_policy : Prop :=
forall (h : VmMaps) (a : word) (nZ : Z),
0 < nZ -> nZ mod page_size = 0 ->
bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
bv_unsigned a + nZ <= alloc_top h ->
region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
bv_unsigned a + nZ <= alloc_ceiling /\ placement_ok_b h (bv_unsigned a) nZ = true.
Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).
Lemma alloc_ceiling_le_alloc_top : ltac2:(TCodec.tc2 tcn__AsanCeil "<'D&Q3r1%211&Q6&Q0&Er2%211%5241p071pS4;1").
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.
Lemma alloc_top_ge_of_ceiling : ltac2:(TCodec.tc2 tcn__AsanCeil "A'D'@&Q3r2%211&Q6&Q0%2241r3&Er4%211%7241p061p0:1pT6>1pS4@1").
Proof. intros h z H Hz. pose proof (alloc_ceiling_le_alloc_top h H). lia. Qed.
Lemma init_sp_ok_init_model : ltac2:(TCodec.tc2 tcn__AsanCeil "N'4'7'R1yR0%211%4211%611'@'C&Ar3%211&Q3&G&Fr7r6r5r4r2%665432:1%811%:11p0<1pS:@1pS>B1pT0F1pSDG1pRLH1pSLG1").
Proof. intros reserved brk0 mbase sp lim inp (Hlo & _ & _). unfold init_sp_ok. cbn. exact Hlo. Qed.
Lemma init_sp_ok_same : ltac2:(TCodec.tc2 tcn__AsanCeil "B'D'9'R1yR0%211&Kr1%211r2%411%93631&Q3r3%211p011p051pS6@1pS4A1").
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.
Lemma init_sp_ok_mkVmMapsFull : ltac2:(TCodec.tc2 tcn__AsanCeil "Q1'D'4'7'R1yR0%211%4211%611'@&Q3r8%211(Hr7r6r5r4r3r2&Kr9%211%:8<9876541%>11p0=1pSBD1pS<B1pRJF1pSNG1pSHF1pS@G1pSJH1pS4Q01").
Proof. intros. unfold init_sp_ok in *. cbn. assumption. Qed.
Lemma page_round_up_Z_ge_all : ltac2:(TCodec.tc2 tcn__AsanCeil "7'@&Q6r1&I%112%4231pT661").
Proof.
intros z. unfold page_round_up_Z, page_size.
pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hr. lia.
Qed.
Lemma mmap_off_aligned_b_0 : ltac2:(TCodec.tc2 tcn__AsanCeil ":'9'0&N&R0yR0z%3221%511(8%93821").
Proof. vm_compute. reflexivity. Qed.
Lemma mmap_anon_b_of_core : ltac2:(TCodec.tc2 tcn__AsanCeil "H'R1yR0%211'@'9&Mr2%211r1%53621'0&Q9+5%2271(8%;3521&Lr4%211%?3915p051p0<1pRNC1pS2E1").
Proof.
intros flags c Hc Hb. unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intro H0.
unfold mmap_flags_core in Hc.
pose proof (Z.land_spec (bv_unsigned flags) MAP_ANONYMOUS 5) as HL. rewrite H0, Z.bits_0 in HL.
pose proof (Z.ldiff_spec (bv_unsigned flags) MAP_NORESERVE 5) as HD. rewrite Hc, Hb in HD.
change (Z.testbit MAP_ANONYMOUS 5) with true in HL. change (Z.testbit MAP_NORESERVE 5) with false in HD.
destruct (Z.testbit (bv_unsigned flags) 5); discriminate.
Qed.
Lemma page_round_up_Z_aligned' : ltac2:(TCodec.tc2 tcn__AsanCeil ";'@'9&Q8&Ir1%211&J%5221z%83921pT6:1").
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma page_round_up_Z_pos' : ltac2:(TCodec.tc2 tcn__AsanCeil ";'@&Q7zr1%3221&Ir2%211%7261p051pT6:1").
Proof. intros z Hz. pose proof (page_round_up_Z_ge z). lia. Qed.
Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.
Lemma at_random_bytes_zero : ltac2:(TCodec.tc2 tcn__AsanCeil "A'9'4'R1y8%211%411&B&R0yT0z%3221%511&>%62:4u@%33;21%@3;51").
Proof. vm_compute. reflexivity. Qed.
Lemma firstn1_skipn_nth : ltac2:(TCodec.tc2 tcn__AsanCeil "N'4'R1y8%211%411'5&;r2&3r3%2271%5241'9&<u1&?r4%23>81%53?41(1&=%14B<5>(6%11D%53E31%=3E71p0?1pS0H1pS8G1pS<I1").
Proof.
induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.
