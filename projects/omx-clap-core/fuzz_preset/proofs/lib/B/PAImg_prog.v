(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: PAListing and PAImg instances (YC4aP) of B_prog_listing (Listing_prog.v).  Image B (asan-ubsan, sha256 d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994), target range [0x816cc, 0x88fb0) (LLVMFuzzerTestOneInput .. end of __wrap_getpid, measured from the symbol table of the unstripped twin), 7737 slots.  Generated from mklisting.py (sha256 f9c5f7b1) at d9b9f6ff0d8 by emit_yc4ap2.py (sha256 6461551b) with pin the internal file pins102.json (sha256 cde4501c); checked by checkprog.py (sha256 a7013998) and by the hub checker checklisting.py (sha256 f605204c) through check_official.py (sha256 7ae3f356): 0 slot failures, 0 failing pairs, 0 objects outside a PT_LOAD. *)


From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YImgTop YC4aP.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Definition B_prog_sigma (s : asym) : Z :=
match s with
| AS_LLVMFuzzerTestOneInput => 0x816cc
| AS_check_no_overread => 0x819f0
| AS_check_bounded_alloc => 0x81f48
| AS_check_as_written => 0x81f78
| AS_check_reject_clean => 0x8208c
| AS_check_reject_clean_starved => 0x820e0
| AS_check_round_trip => 0x82828
| AS_parse_noting => 0x81ed0
| AS_same => 0x8313c
| AS_ex_value => 0x8352c
| AS_ex_ws => 0x84274
| AS_ex_string => 0x84350
| AS_ex_word => 0x848d4
| AS_ex_hex4 => 0x84a50
| AS_ex_utf8 => 0x84b54
| AS_round_trip_text => 0x84e4c
| AS_tx_put => 0x851d0
| AS_tx_value => 0x85440
| AS_tx_string => 0x858c0
| AS_tx_line => 0x85c34
| AS_asan_module_ctor => 0x85ca0
| AS_asan_module_dtor => 0x85cd8
| AS_fuzz_malloc => 0x85d08
| AS_own => 0x85dbc
| AS_fuzz_realloc => 0x85eb4
| AS_fuzz_strdup => 0x860e0
| AS_fuzz_free => 0x8613c
| AS_fuzz_alloc_live => 0x8626c
| AS_fuzz_alloc_peak => 0x86278
| AS_fuzz_alloc_peak_reset => 0x86284
| AS_fuzz_alloc_count => 0x86298
| AS_fuzz_alloc_fail => 0x862a4
| AS_fuzz_alloc_ran_out => 0x862c8
| AS_fuzz_alloc_ran_out_reset => 0x862d4
| AS_pj_parse => 0x862ec
| AS_parse_value => 0x8637c
| AS_skip_ws => 0x86948
| AS_pj_free => 0x86a24
| AS_pj_get => 0x86c44
| AS_pj_get_str => 0x86e04
| AS_pj_set => 0x86e8c
| AS_grow => 0x87058
| AS_pj_string => 0x87208
| AS_pj_write => 0x872cc
| AS_write_value => 0x87348
| AS_put => 0x877d4
| AS_parse_items => 0x87a38
| AS_parse_string => 0x880fc
| AS_literal => 0x88704
| AS_hex4 => 0x88850
| AS_put_utf8 => 0x88954
| AS_put_string => 0x88b90
| AS_indent => 0x88f30
| AS___wrap_getenv => 0x88fa0
| AS___wrap_getpid => 0x88fa8
| AS___wrap_bcmp => 0x42e18
| AS___wrap_free => 0x53820
| AS___wrap_malloc => 0x53824
| AS___wrap_realloc => 0x53828
| AS___wrap_snprintf => 0x42e44
| AS___wrap_strcmp => 0x42e0c
| AS___wrap_strlen => 0x42e04
| AS___interceptor_bcmp => 0x44524
| AS___interceptor_free => 0x5382c
| AS___interceptor_malloc => 0x539fc
| AS___interceptor_realloc => 0x53c24
| AS___interceptor_snprintf => 0x466f8
| AS___interceptor_strcmp => 0x433c0
| AS___interceptor_strlen => 0x42e94
| AS_abort => 0x8f870
| AS_strtod => 0x9b740
| AS_raise => 0x94acc
| AS___block_all_sigs => 0x94a70
| AS___lock => 0x9c3d4
| AS__Exit => 0x8f904
| AS___funcs_on_exit => 0x8f950
| AS___libc_exit_fini => 0x8fae8
| AS___stdio_exit => 0x958c8
| AS_exit => 0x8fb34
| AS_strcmp => 0x9c11c
| AS___asan_handle_no_return => 0x5a92c
| AS___asan_init => 0x5aa94
| AS___asan_memcpy => 0x524d0
| AS___asan_memset => 0x5296c
| AS___asan_poison_memory_region => 0x55044
| AS___asan_register_elf_globals => 0x40d40
| AS___asan_set_shadow_f5 => 0x557e0
| AS___asan_stack_malloc_0 => 0x3dc34
| AS___asan_stack_malloc_1 => 0x3dda8
| AS___asan_stack_malloc_3 => 0x3df38
| AS___asan_unpoison_memory_region => 0x551e4
| AS___asan_unregister_elf_globals => 0x40dac
| AS___asan_version_mismatch_check_v8 => 0x5ab28
| AS___asan_report_load1 => 0x59930
| AS___asan_report_load16 => 0x59bb0
| AS___asan_report_load2 => 0x599d0
| AS___asan_report_load4 => 0x59a70
| AS___asan_report_load8 => 0x59b10
| AS___asan_report_load_n => 0x59f70
| AS___asan_report_store1 => 0x59c50
| AS___asan_report_store16 => 0x59ed0
| AS___asan_report_store2 => 0x59cf0
| AS___asan_report_store4 => 0x59d90
| AS___asan_report_store8 => 0x59e30
| AS___asan_report_store_n => 0x5a010
| AS___asan_report_exp_load1 => 0x59980
| AS___asan_report_exp_load16 => 0x59c00
| AS___asan_report_exp_load2 => 0x59a20
| AS___asan_report_exp_load4 => 0x59ac0
| AS___asan_report_exp_load8 => 0x59b60
| AS___asan_report_exp_load_n => 0x59fc0
| AS___asan_report_exp_store1 => 0x59ca0
| AS___asan_report_exp_store16 => 0x59f20
| AS___asan_report_exp_store2 => 0x59d40
| AS___asan_report_exp_store4 => 0x59de0
| AS___asan_report_exp_store8 => 0x59e80
| AS___asan_report_exp_store_n => 0x5a060
| AS_read_members => 0x82554
| AS_padded => 0x830a8
| AS_fuzz_pick => 0x84da4
| AS_fuzz_alloc_most => 0x862e0
end.
Lemma B_prog_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma B_prog_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma B_prog_range : forall a, in_img rsegs a -> IMG_LO_B <= a < IMG_TOP_B.
Proof.
intros a (sg & Hin & Hr). unfold IMG_LO_B, IMG_TOP_B.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Definition B_prog_relro_lo : Z := 0xa2240.
Definition B_prog_relro_hi : Z := 0xa4000.
Lemma B_prog_relro : forall a, B_prog_relro_lo <= a < B_prog_relro_hi -> in_img rsegs a.
Proof.
intros a Ha. unfold B_prog_relro_lo, B_prog_relro_hi in Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma B_prog_cover : forall ly S md, ALedger rsegs ly S md -> fst (ly_img ly) <= IMG_LO_B /\ IMG_TOP_B <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. unfold IMG_LO_B, IMG_TOP_B. split.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
Definition B_prog_tpi : ptree asym := Eval vm_compute in (ptree_of_list B_prog_listing).
Lemma B_prog_tpi_eq : ptree_of_list B_prog_listing = B_prog_tpi.
Proof. vm_compute; reflexivity. Qed.
Definition B_prog_tw : ctable := Eval vm_compute in (tw_of 0 B_prog_listing).
#[export] Instance PL_prog_B : PAListing B_prog_listing :=
{| pl_tpi := B_prog_tpi; pl_tpi_eq := B_prog_tpi_eq; pl_tw := B_prog_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.
Definition B_prog_tbl : ctable := Eval vm_compute in (build_table rsegs B_prog_base B_prog_nslots TEmpty).
Lemma B_prog_tbl_eq : B_prog_tbl = build_table rsegs B_prog_base B_prog_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl B_prog_tbl). Qed.
Lemma B_prog_tbl_ok : table_ok rsegs B_prog_tbl.
Proof. rewrite B_prog_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition B_prog_obj (i : nat) : Z :=
match i with
| 0%nat => 0xa2850
| 1%nat => 0xa28a8
| 2%nat => 0x10000
| 3%nat => 0xa2660
| 4%nat => 0xa34c8
| 5%nat => 0xa34d0
| 6%nat => 0xa8040
| 7%nat => 0x5ddde0
| 8%nat => 0xa6e00
| 9%nat => 0x5ddda0
| 10%nat => 0x5dddc0
| 11%nat => 0x5dde00
| 12%nat => 0xab6f8
| 13%nat => 0x5ddd80
| 14%nat => 0xa6e20
| _ => 0xa2850
end.
Definition B_prog_hi (j : nat) : Z :=
match j with
| 0%nat => 0xa2718
| 1%nat => 0xa271c
| 2%nat => 0x1d778
| 3%nat => 0x81784
| 4%nat => 0x5dd7f0
| 5%nat => 0xa2a3c
| 6%nat => 0xa2a40
| 7%nat => 0x18aa8
| 8%nat => 0x81aac
| 9%nat => 0x5ddc40
| 10%nat => 0x5ddff0
| 11%nat => 0x5de020
| 12%nat => 0x210a0
| 13%nat => 0xa2134
| 14%nat => 0xa2138
| 15%nat => 0x12194
| 16%nat => 0x82198
| 17%nat => 0x5de2bc
| 18%nat => 0xa258c
| 19%nat => 0x2159c
| 20%nat => 0x215b0
| 21%nat => 0xa25cc
| 22%nat => 0x21618
| 23%nat => 0x21628
| 24%nat => 0x2167c
| 25%nat => 0x21698
| 26%nat => 0x21774
| 27%nat => 0x2178c
| 28%nat => 0xa2800
| 29%nat => 0xa2870
| 30%nat => 0xa2874
| 31%nat => 0x198d4
| 32%nat => 0x828d8
| 33%nat => 0x21a74
| 34%nat => 0x20a98
| 35%nat => 0x5ddab0
| 36%nat => 0x20cf4
| 37%nat => 0x20f7c
| 38%nat => 0x21010
| 39%nat => 0x5de10c
| 40%nat => 0xa2188
| 41%nat => 0xa2578
| 42%nat => 0xa257c
| 43%nat => 0x135d8
| 44%nat => 0x835dc
| 45%nat => 0x216c4
| 46%nat => 0x21790
| 47%nat => 0x20948
| 48%nat => 0xa2284
| 49%nat => 0xa2394
| 50%nat => 0xa290c
| 51%nat => 0xa2a5c
| 52%nat => 0xa2b5c
| 53%nat => 0xa2db4
| 54%nat => 0xa2e9c
| 55%nat => 0xa2ea0
| 56%nat => 0x16efc
| 57%nat => 0x84f00
| 58%nat => 0x20f90
| 59%nat => 0x20fbc
| 60%nat => 0x5de004
| 61%nat => 0xa221c
| 62%nat => 0x5de39c
| 63%nat => 0xa2498
| 64%nat => 0x214c8
| 65%nat => 0x214e8
| 66%nat => 0x214f4
| 67%nat => 0x21558
| 68%nat => 0x2155c
| 69%nat => 0x21560
| 70%nat => 0x21718
| 71%nat => 0x207bc
| 72%nat => 0x207fc
| 73%nat => 0x2080c
| 74%nat => 0x2181c
| 75%nat => 0xa2910
| 76%nat => 0x1e96c
| 77%nat => 0x85970
| 78%nat => 0x219c0
| 79%nat => 0x21a0c
| 80%nat => 0x21a10
| 81%nat => 0x20b5c
| 82%nat => 0x20c50
| 83%nat => 0x20c68
| 84%nat => 0xa3cb0
| 85%nat => 0xa3cb4
| 86%nat => 0xa7cc0
| 87%nat => 0xa2ce0
| 88%nat => 0xa2ce4
| 89%nat => 0xa7cf0
| 90%nat => 0x5ddd18
| 91%nat => 0xa6d20
| 92%nat => 0x5ddd68
| 93%nat => 0x5ddd70
| 94%nat => 0xa6d90
| 95%nat => 0x5ddd9c
| 96%nat => 0xa2dcc
| 97%nat => 0x5dde4c
| 98%nat => 0x5dde54
| 99%nat => 0xa2ed4
| 100%nat => 0x5ddedc
| 101%nat => 0xa6ee4
| 102%nat => 0x5ddf4c
| 103%nat => 0x5ddf54
| 104%nat => 0xa6f74
| 105%nat => 0x5ddf80
| 106%nat => 0x5de01c
| 107%nat => 0x5de070
| 108%nat => 0xa7090
| 109%nat => 0x5de09c
| 110%nat => 0xa2168
| 111%nat => 0x5de1f0
| 112%nat => 0x5de26c
| 113%nat => 0x5de278
| 114%nat => 0x5de284
| 115%nat => 0x5de28c
| 116%nat => 0x5de298
| 117%nat => 0x5de2a4
| 118%nat => 0xa72bc
| 119%nat => 0x5de2c8
| 120%nat => 0x5de2d4
| 121%nat => 0xa72e0
| 122%nat => 0xa23c8
| 123%nat => 0xa23cc
| 124%nat => 0x19428
| 125%nat => 0x8642c
| 126%nat => 0x21584
| 127%nat => 0x21630
| 128%nat => 0xa2958
| 129%nat => 0xa2a6c
| 130%nat => 0xa2c88
| 131%nat => 0xa2e10
| 132%nat => 0xa2eb0
| 133%nat => 0xa2098
| 134%nat => 0xa2220
| 135%nat => 0x21264
| 136%nat => 0x2130c
| 137%nat => 0xa23a0
| 138%nat => 0x213d4
| 139%nat => 0x213f4
| 140%nat => 0x21400
| 141%nat => 0x2141c
| 142%nat => 0x21428
| 143%nat => 0x2147c
| 144%nat => 0x21614
| 145%nat => 0x21640
| 146%nat => 0x216f0
| 147%nat => 0x21710
| 148%nat => 0x21720
| 149%nat => 0x21730
| 150%nat => 0xa2820
| 151%nat => 0xa2a88
| 152%nat => 0xa2140
| 153%nat => 0xa273c
| 154%nat => 0xa285c
| 155%nat => 0xa295c
| 156%nat => 0xa2bdc
| 157%nat => 0xa2be0
| 158%nat => 0x11c3c
| 159%nat => 0x88c40
| 160%nat => 0x21c90
| 161%nat => 0x21cd0
| 162%nat => 0x21cd4
| 163%nat => 0x21cd8
| 164%nat => 0x21cdc
| 165%nat => 0x21ce0
| 166%nat => 0x20e68
| 167%nat => 0x20f50
| 168%nat => 0x20f68
| _ => 0
end.
Definition B_prog_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then B_prog_base else if (a <? A_HI 0)%nat then B_prog_obj (a - A_OBJ 0) else B_prog_hi (a - A_HI 0).
Lemma B_prog_val_range : forall a, 0 <= B_prog_val a < 2 ^ 64.
Proof.
intros a. unfold B_prog_val. destruct (Nat.eqb a A_TEXT); [unfold B_prog_base; zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold B_prog_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 15 (destruct m as [|m]; [zlit|]). zlit.
- unfold B_prog_hi. generalize (a - A_HI 0)%nat as m. intros m. do 169 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma B_prog_cert : pi_check asym (clookup B_prog_tbl) B_prog_val B_prog_sigma B_prog_listing = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma B_prog_obj_img : forall i, (i < 39)%nat -> IMG_LO_B <= B_prog_val (A_OBJ i) /\ B_prog_val (A_OBJ i) + 8 <= IMG_TOP_B.
Proof. intros i Hi. unfold IMG_LO_B, IMG_TOP_B. do 39 (destruct i as [|i]; [unfold B_prog_val, B_prog_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]). exfalso; lia.
Qed.
Lemma B_prog_obj0 : B_prog_val (A_OBJ 0) = 0xa2850.
Proof. vm_compute. reflexivity. Qed.
Lemma B_prog_obj1 : B_prog_val (A_OBJ 1) = 0xa28a8.
Proof. vm_compute. reflexivity. Qed.
Lemma B_prog_obj12 : B_prog_val (A_OBJ 12) = 0xab6f8.
Proof. vm_compute. reflexivity. Qed.
Lemma B_prog_got_uar_disj : (B_prog_val (A_OBJ 1) + 8 <= B_prog_val (A_OBJ 0) \/ B_prog_val (A_OBJ 0) + 8 <= B_prog_val (A_OBJ 1))
/\ (B_prog_val (A_OBJ 1) + 8 <= B_prog_val (A_OBJ 12) \/ B_prog_val (A_OBJ 12) + 8 <= B_prog_val (A_OBJ 1)).
Proof. unfold B_prog_val, B_prog_obj, A_OBJ, A_TEXT, A_HI. cbn. lia. Qed.
#[export] Instance PI_prog_B : PAImg B_prog_listing := {|
pa_segs := rsegs; pa_tbl := B_prog_tbl; pa_tbl_ok := B_prog_tbl_ok; pa_val := B_prog_val; pa_sigma := B_prog_sigma;
pa_cert := B_prog_cert; pa_B_ok := ltac:(unfold B_prog_val, B_prog_base; cbn; lia); pa_val_range := B_prog_val_range;
pa_wx := B_prog_wx; pa_segs_low := B_prog_segs_low; pa_lo := IMG_LO_B; pa_hi := IMG_TOP_B; pa_img_range := B_prog_range; pa_img_cover := B_prog_cover;
pa_obj_img := B_prog_obj_img; pa_relro_lo := B_prog_relro_lo; pa_relro_hi := B_prog_relro_hi; pa_relro_img := B_prog_relro |}.
Definition B_prog_slot (s : asym) : nat := Z.to_nat ((B_prog_sigma s - B_prog_base) / 4).
Lemma B_entry_LLVMFuzzerTestOneInput : B_prog_sigma AS_LLVMFuzzerTestOneInput = 0x816cc /\ B_prog_slot AS_LLVMFuzzerTestOneInput = 0%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_check_no_overread : B_prog_sigma AS_check_no_overread = 0x819f0 /\ B_prog_slot AS_check_no_overread = 201%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_parse_noting : B_prog_sigma AS_parse_noting = 0x81ed0 /\ B_prog_slot AS_parse_noting = 513%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_check_bounded_alloc : B_prog_sigma AS_check_bounded_alloc = 0x81f48 /\ B_prog_slot AS_check_bounded_alloc = 543%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_check_as_written : B_prog_sigma AS_check_as_written = 0x81f78 /\ B_prog_slot AS_check_as_written = 555%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_check_reject_clean : B_prog_sigma AS_check_reject_clean = 0x8208c /\ B_prog_slot AS_check_reject_clean = 624%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_check_reject_clean_starved : B_prog_sigma AS_check_reject_clean_starved = 0x820e0 /\ B_prog_slot AS_check_reject_clean_starved = 645%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_read_members : B_prog_sigma AS_read_members = 0x82554 /\ B_prog_slot AS_read_members = 930%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_check_round_trip : B_prog_sigma AS_check_round_trip = 0x82828 /\ B_prog_slot AS_check_round_trip = 1111%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_padded : B_prog_sigma AS_padded = 0x830a8 /\ B_prog_slot AS_padded = 1655%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_same : B_prog_sigma AS_same = 0x8313c /\ B_prog_slot AS_same = 1692%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_ex_value : B_prog_sigma AS_ex_value = 0x8352c /\ B_prog_slot AS_ex_value = 1944%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_ex_ws : B_prog_sigma AS_ex_ws = 0x84274 /\ B_prog_slot AS_ex_ws = 2794%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_ex_string : B_prog_sigma AS_ex_string = 0x84350 /\ B_prog_slot AS_ex_string = 2849%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_ex_word : B_prog_sigma AS_ex_word = 0x848d4 /\ B_prog_slot AS_ex_word = 3202%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_ex_hex4 : B_prog_sigma AS_ex_hex4 = 0x84a50 /\ B_prog_slot AS_ex_hex4 = 3297%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_ex_utf8 : B_prog_sigma AS_ex_utf8 = 0x84b54 /\ B_prog_slot AS_ex_utf8 = 3362%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_pick : B_prog_sigma AS_fuzz_pick = 0x84da4 /\ B_prog_slot AS_fuzz_pick = 3510%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_round_trip_text : B_prog_sigma AS_round_trip_text = 0x84e4c /\ B_prog_slot AS_round_trip_text = 3552%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_tx_put : B_prog_sigma AS_tx_put = 0x851d0 /\ B_prog_slot AS_tx_put = 3777%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_tx_value : B_prog_sigma AS_tx_value = 0x85440 /\ B_prog_slot AS_tx_value = 3933%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_tx_string : B_prog_sigma AS_tx_string = 0x858c0 /\ B_prog_slot AS_tx_string = 4221%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_tx_line : B_prog_sigma AS_tx_line = 0x85c34 /\ B_prog_slot AS_tx_line = 4442%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_asan_module_ctor : B_prog_sigma AS_asan_module_ctor = 0x85ca0 /\ B_prog_slot AS_asan_module_ctor = 4469%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_asan_module_dtor : B_prog_sigma AS_asan_module_dtor = 0x85cd8 /\ B_prog_slot AS_asan_module_dtor = 4483%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_malloc : B_prog_sigma AS_fuzz_malloc = 0x85d08 /\ B_prog_slot AS_fuzz_malloc = 4495%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_own : B_prog_sigma AS_own = 0x85dbc /\ B_prog_slot AS_own = 4540%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_realloc : B_prog_sigma AS_fuzz_realloc = 0x85eb4 /\ B_prog_slot AS_fuzz_realloc = 4602%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_strdup : B_prog_sigma AS_fuzz_strdup = 0x860e0 /\ B_prog_slot AS_fuzz_strdup = 4741%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_free : B_prog_sigma AS_fuzz_free = 0x8613c /\ B_prog_slot AS_fuzz_free = 4764%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_alloc_live : B_prog_sigma AS_fuzz_alloc_live = 0x8626c /\ B_prog_slot AS_fuzz_alloc_live = 4840%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_alloc_peak : B_prog_sigma AS_fuzz_alloc_peak = 0x86278 /\ B_prog_slot AS_fuzz_alloc_peak = 4843%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_alloc_peak_reset : B_prog_sigma AS_fuzz_alloc_peak_reset = 0x86284 /\ B_prog_slot AS_fuzz_alloc_peak_reset = 4846%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_alloc_count : B_prog_sigma AS_fuzz_alloc_count = 0x86298 /\ B_prog_slot AS_fuzz_alloc_count = 4851%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_alloc_fail : B_prog_sigma AS_fuzz_alloc_fail = 0x862a4 /\ B_prog_slot AS_fuzz_alloc_fail = 4854%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_alloc_ran_out : B_prog_sigma AS_fuzz_alloc_ran_out = 0x862c8 /\ B_prog_slot AS_fuzz_alloc_ran_out = 4863%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_alloc_ran_out_reset : B_prog_sigma AS_fuzz_alloc_ran_out_reset = 0x862d4 /\ B_prog_slot AS_fuzz_alloc_ran_out_reset = 4866%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_fuzz_alloc_most : B_prog_sigma AS_fuzz_alloc_most = 0x862e0 /\ B_prog_slot AS_fuzz_alloc_most = 4869%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_pj_parse : B_prog_sigma AS_pj_parse = 0x862ec /\ B_prog_slot AS_pj_parse = 4872%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_parse_value : B_prog_sigma AS_parse_value = 0x8637c /\ B_prog_slot AS_parse_value = 4908%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_skip_ws : B_prog_sigma AS_skip_ws = 0x86948 /\ B_prog_slot AS_skip_ws = 5279%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_pj_free : B_prog_sigma AS_pj_free = 0x86a24 /\ B_prog_slot AS_pj_free = 5334%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_pj_get : B_prog_sigma AS_pj_get = 0x86c44 /\ B_prog_slot AS_pj_get = 5470%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_pj_get_str : B_prog_sigma AS_pj_get_str = 0x86e04 /\ B_prog_slot AS_pj_get_str = 5582%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_pj_set : B_prog_sigma AS_pj_set = 0x86e8c /\ B_prog_slot AS_pj_set = 5616%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_grow : B_prog_sigma AS_grow = 0x87058 /\ B_prog_slot AS_grow = 5731%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_pj_string : B_prog_sigma AS_pj_string = 0x87208 /\ B_prog_slot AS_pj_string = 5839%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_pj_write : B_prog_sigma AS_pj_write = 0x872cc /\ B_prog_slot AS_pj_write = 5888%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_write_value : B_prog_sigma AS_write_value = 0x87348 /\ B_prog_slot AS_write_value = 5919%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_put : B_prog_sigma AS_put = 0x877d4 /\ B_prog_slot AS_put = 6210%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_parse_items : B_prog_sigma AS_parse_items = 0x87a38 /\ B_prog_slot AS_parse_items = 6363%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_parse_string : B_prog_sigma AS_parse_string = 0x880fc /\ B_prog_slot AS_parse_string = 6796%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_literal : B_prog_sigma AS_literal = 0x88704 /\ B_prog_slot AS_literal = 7182%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_hex4 : B_prog_sigma AS_hex4 = 0x88850 /\ B_prog_slot AS_hex4 = 7265%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_put_utf8 : B_prog_sigma AS_put_utf8 = 0x88954 /\ B_prog_slot AS_put_utf8 = 7330%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_put_string : B_prog_sigma AS_put_string = 0x88b90 /\ B_prog_slot AS_put_string = 7473%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry_indent : B_prog_sigma AS_indent = 0x88f30 /\ B_prog_slot AS_indent = 7705%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry___wrap_getenv : B_prog_sigma AS___wrap_getenv = 0x88fa0 /\ B_prog_slot AS___wrap_getenv = 7733%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_entry___wrap_getpid : B_prog_sigma AS___wrap_getpid = 0x88fa8 /\ B_prog_slot AS___wrap_getpid = 7735%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma B_alias_hints_ok : forall E, img_env B_prog_val A_LIM E -> alias_ok E B_alias_hints.
Proof.
intros E HE. unfold B_alias_hints.
repeat (split; [cbn [sv_denot]; rewrite !HE by (unfold A_TEXT, A_LIM, A_OBJ, A_HI; lia); f_equal; vm_compute; reflexivity|]).
exact I.
Qed.
End c.
