(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: PAListing and PAImg instances (YC4aP) of A_prog_listing (Listing_prog.v).  Image A (asan, sha256 1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44), target range [0x815e0, 0x88760) (LLVMFuzzerTestOneInput .. end of __wrap_getpid, measured from the symbol table of the unstripped twin), 7264 slots.  Generated from mklisting.py (sha256 f9c5f7b1) at d9b9f6ff0d8 by emit_yc4ap2.py (sha256 6461551b) with pin the internal file pins102.json (sha256 cde4501c); checked by checkprog.py (sha256 a7013998) and by the hub checker checklisting.py (sha256 f605204c) through check_official.py (sha256 7ae3f356): 0 slot failures, 0 failing pairs, 0 objects outside a PT_LOAD. *)


From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YImgTop YC4aP.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Definition A_prog_sigma (s : asym) : Z :=
match s with
| AS_LLVMFuzzerTestOneInput => 0x815e0
| AS_check_no_overread => 0x81904
| AS_check_bounded_alloc => 0x81f8c
| AS_check_as_written => 0x81fb8
| AS_check_reject_clean => 0x82110
| AS_check_reject_clean_starved => 0x82160
| AS_check_round_trip => 0x82870
| AS_parse_noting => 0x81f14
| AS_same => 0x82fb8
| AS_ex_value => 0x832a4
| AS_ex_ws => 0x0
| AS_ex_string => 0x84034
| AS_ex_word => 0x8452c
| AS_ex_hex4 => 0x84688
| AS_ex_utf8 => 0x84764
| AS_round_trip_text => 0x8496c
| AS_tx_put => 0x84cec
| AS_tx_value => 0x84f04
| AS_tx_string => 0x852f4
| AS_tx_line => 0x85654
| AS_asan_module_ctor => 0x856c0
| AS_asan_module_dtor => 0x856f8
| AS_fuzz_malloc => 0x85728
| AS_own => 0x0
| AS_fuzz_realloc => 0x858ac
| AS_fuzz_strdup => 0x85c28
| AS_fuzz_free => 0x85c84
| AS_fuzz_alloc_live => 0x85da0
| AS_fuzz_alloc_peak => 0x85dac
| AS_fuzz_alloc_peak_reset => 0x85db8
| AS_fuzz_alloc_count => 0x85dcc
| AS_fuzz_alloc_fail => 0x85dd8
| AS_fuzz_alloc_ran_out => 0x85dfc
| AS_fuzz_alloc_ran_out_reset => 0x85e08
| AS_pj_parse => 0x85e20
| AS_parse_value => 0x85f10
| AS_skip_ws => 0x0
| AS_pj_free => 0x864e4
| AS_pj_get => 0x86694
| AS_pj_get_str => 0x867dc
| AS_pj_set => 0x8685c
| AS_grow => 0x869bc
| AS_pj_string => 0x86b58
| AS_pj_write => 0x86c10
| AS_write_value => 0x86c8c
| AS_put => 0x87094
| AS_parse_items => 0x87298
| AS_parse_string => 0x8794c
| AS_literal => 0x87f60
| AS_hex4 => 0x88088
| AS_put_utf8 => 0x88164
| AS_put_string => 0x8836c
| AS_indent => 0x886e0
| AS___wrap_getenv => 0x88750
| AS___wrap_getpid => 0x88758
| AS___wrap_bcmp => 0x42d2c
| AS___wrap_free => 0x53734
| AS___wrap_malloc => 0x53738
| AS___wrap_realloc => 0x5373c
| AS___wrap_snprintf => 0x42d58
| AS___wrap_strcmp => 0x42d20
| AS___wrap_strlen => 0x42d18
| AS___interceptor_bcmp => 0x44438
| AS___interceptor_free => 0x53740
| AS___interceptor_malloc => 0x53910
| AS___interceptor_realloc => 0x53b38
| AS___interceptor_snprintf => 0x4660c
| AS___interceptor_strcmp => 0x432d4
| AS___interceptor_strlen => 0x42da8
| AS_abort => 0x8f020
| AS_strtod => 0x9aef0
| AS_raise => 0x9427c
| AS___block_all_sigs => 0x94220
| AS___lock => 0x9bb84
| AS__Exit => 0x8f0b4
| AS___funcs_on_exit => 0x8f100
| AS___libc_exit_fini => 0x8f298
| AS___stdio_exit => 0x95078
| AS_exit => 0x8f2e4
| AS_strcmp => 0x9b8cc
| AS___asan_handle_no_return => 0x5a840
| AS___asan_init => 0x5a9a8
| AS___asan_memcpy => 0x523e4
| AS___asan_memset => 0x52880
| AS___asan_poison_memory_region => 0x54f58
| AS___asan_register_elf_globals => 0x40c54
| AS___asan_set_shadow_f5 => 0x556f4
| AS___asan_stack_malloc_0 => 0x3db48
| AS___asan_stack_malloc_1 => 0x3dcbc
| AS___asan_stack_malloc_3 => 0x3de4c
| AS___asan_unpoison_memory_region => 0x550f8
| AS___asan_unregister_elf_globals => 0x40cc0
| AS___asan_version_mismatch_check_v8 => 0x5aa3c
| AS___asan_report_load1 => 0x59844
| AS___asan_report_load16 => 0x59ac4
| AS___asan_report_load2 => 0x598e4
| AS___asan_report_load4 => 0x59984
| AS___asan_report_load8 => 0x59a24
| AS___asan_report_load_n => 0x59e84
| AS___asan_report_store1 => 0x59b64
| AS___asan_report_store16 => 0x59de4
| AS___asan_report_store2 => 0x59c04
| AS___asan_report_store4 => 0x59ca4
| AS___asan_report_store8 => 0x59d44
| AS___asan_report_store_n => 0x59f24
| AS___asan_report_exp_load1 => 0x59894
| AS___asan_report_exp_load16 => 0x59b14
| AS___asan_report_exp_load2 => 0x59934
| AS___asan_report_exp_load4 => 0x599d4
| AS___asan_report_exp_load8 => 0x59a74
| AS___asan_report_exp_load_n => 0x59ed4
| AS___asan_report_exp_store1 => 0x59bb4
| AS___asan_report_exp_store16 => 0x59e34
| AS___asan_report_exp_store2 => 0x59c54
| AS___asan_report_exp_store4 => 0x59cf4
| AS___asan_report_exp_store8 => 0x59d94
| AS___asan_report_exp_store_n => 0x59f74
| AS_read_members => 0x825f8
| AS_padded => 0x0
| AS_fuzz_pick => 0x0
| AS_fuzz_alloc_most => 0x85e14
end.
Lemma A_prog_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma A_prog_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma A_prog_range : forall a, in_img rsegs a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a (sg & Hin & Hr). unfold IMG_LO, IMG_TOP.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Definition A_prog_relro_lo : Z := 0xa19f0.
Definition A_prog_relro_hi : Z := 0xa3000.
Lemma A_prog_relro : forall a, A_prog_relro_lo <= a < A_prog_relro_hi -> in_img rsegs a.
Proof.
intros a Ha. unfold A_prog_relro_lo, A_prog_relro_hi in Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma A_prog_cover : forall ly S md, ALedger rsegs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. unfold IMG_LO, IMG_TOP. split.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
Definition A_prog_tpi : ptree asym := Eval vm_compute in (ptree_of_list A_prog_listing).
Lemma A_prog_tpi_eq : ptree_of_list A_prog_listing = A_prog_tpi.
Proof. vm_compute; reflexivity. Qed.
Definition A_prog_tw : ctable := Eval vm_compute in (tw_of 0 A_prog_listing).
#[export] Instance PL_prog_A : PAListing A_prog_listing :=
{| pl_tpi := A_prog_tpi; pl_tpi_eq := A_prog_tpi_eq; pl_tw := A_prog_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.
Definition A_prog_tbl : ctable := Eval vm_compute in (build_table rsegs A_prog_base A_prog_nslots TEmpty).
Lemma A_prog_tbl_eq : A_prog_tbl = build_table rsegs A_prog_base A_prog_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl A_prog_tbl). Qed.
Lemma A_prog_tbl_ok : table_ok rsegs A_prog_tbl.
Proof. rewrite A_prog_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition A_prog_obj (i : nat) : Z :=
match i with
| 0%nat => 0xa2010
| 1%nat => 0xa2068
| 2%nat => 0x10000
| 3%nat => 0xa1e20
| 4%nat => 0xa2c88
| 5%nat => 0xa2c90
| 6%nat => 0xa7800
| 7%nat => 0x5dd5a0
| 8%nat => 0xa65c0
| 9%nat => 0x5dd560
| 10%nat => 0x5dd580
| 11%nat => 0x5dd5c0
| 12%nat => 0xaaeb8
| 13%nat => 0x5dd540
| 14%nat => 0xa65e0
| _ => 0xa2010
end.
Definition A_prog_hi (j : nat) : Z :=
match j with
| 0%nat => 0xa262c
| 1%nat => 0xa2630
| 2%nat => 0x1e68c
| 3%nat => 0x81698
| 4%nat => 0x5dd704
| 5%nat => 0xa1950
| 6%nat => 0xa1954
| 7%nat => 0x189b0
| 8%nat => 0x819b4
| 9%nat => 0x5dda98
| 10%nat => 0xa1fd4
| 11%nat => 0x5dd028
| 12%nat => 0x5dd0b4
| 13%nat => 0x21124
| 14%nat => 0xa21b4
| 15%nat => 0xa21b8
| 16%nat => 0x12214
| 17%nat => 0x82218
| 18%nat => 0x5dd324
| 19%nat => 0x21640
| 20%nat => 0x21654
| 21%nat => 0xa1670
| 22%nat => 0x216b8
| 23%nat => 0x216c8
| 24%nat => 0x21714
| 25%nat => 0x2172c
| 26%nat => 0x217c0
| 27%nat => 0x217d4
| 28%nat => 0xa1848
| 29%nat => 0xa18b8
| 30%nat => 0xa18bc
| 31%nat => 0x1991c
| 32%nat => 0x82920
| 33%nat => 0x21ab0
| 34%nat => 0x20ad8
| 35%nat => 0x5ddaf0
| 36%nat => 0x20d34
| 37%nat => 0x20ecc
| 38%nat => 0x20f2c
| 39%nat => 0xa1ff0
| 40%nat => 0xa22f0
| 41%nat => 0xa22f4
| 42%nat => 0x1934c
| 43%nat => 0x83350
| 44%nat => 0x21494
| 45%nat => 0x21554
| 46%nat => 0x21748
| 47%nat => 0xa206c
| 48%nat => 0xa2564
| 49%nat => 0xa2694
| 50%nat => 0xa276c
| 51%nat => 0xa19bc
| 52%nat => 0xa19c0
| 53%nat => 0x16a1c
| 54%nat => 0x84a20
| 55%nat => 0x20ab0
| 56%nat => 0x20adc
| 57%nat => 0x5ddb24
| 58%nat => 0xa1d28
| 59%nat => 0x5dce74
| 60%nat => 0xa1f44
| 61%nat => 0x20f7c
| 62%nat => 0x20f9c
| 63%nat => 0x20fa8
| 64%nat => 0x20ffc
| 65%nat => 0x21000
| 66%nat => 0x21004
| 67%nat => 0x21150
| 68%nat => 0x211f4
| 69%nat => 0x21234
| 70%nat => 0x21244
| 71%nat => 0x21254
| 72%nat => 0xa2340
| 73%nat => 0xa2344
| 74%nat => 0x1e3a0
| 75%nat => 0x853a4
| 76%nat => 0x213f8
| 77%nat => 0x21438
| 78%nat => 0x2143c
| 79%nat => 0x21580
| 80%nat => 0x21670
| 81%nat => 0x21688
| 82%nat => 0xa26d0
| 83%nat => 0xa26d4
| 84%nat => 0xa76e0
| 85%nat => 0xa2700
| 86%nat => 0xa2704
| 87%nat => 0xa7710
| 88%nat => 0xa2740
| 89%nat => 0x5dd748
| 90%nat => 0xa6750
| 91%nat => 0x5dd7fc
| 92%nat => 0x5dd804
| 93%nat => 0x5dd824
| 94%nat => 0x5dd82c
| 95%nat => 0xa684c
| 96%nat => 0x5dd864
| 97%nat => 0xa18dc
| 98%nat => 0x5dd8e4
| 99%nat => 0xa68ec
| 100%nat => 0x5dd948
| 101%nat => 0x5dd950
| 102%nat => 0xa6970
| 103%nat => 0x5dd980
| 104%nat => 0x5dda0c
| 105%nat => 0x5ddab0
| 106%nat => 0x5ddad4
| 107%nat => 0xa6af4
| 108%nat => 0x5ddb00
| 109%nat => 0xa1ca0
| 110%nat => 0x5ddd28
| 111%nat => 0x5dcda0
| 112%nat => 0x5dcdac
| 113%nat => 0x5dcdb8
| 114%nat => 0x5dcdc0
| 115%nat => 0x5dcdcc
| 116%nat => 0x5dcdd8
| 117%nat => 0xa5df0
| 118%nat => 0x5dcdfc
| 119%nat => 0x5dce08
| 120%nat => 0xa5e14
| 121%nat => 0xa1e34
| 122%nat => 0xa1f5c
| 123%nat => 0xa1f60
| 124%nat => 0x18fb8
| 125%nat => 0x85fbc
| 126%nat => 0x210e4
| 127%nat => 0x21168
| 128%nat => 0x21270
| 129%nat => 0xa2520
| 130%nat => 0xa26c8
| 131%nat => 0xa27e8
| 132%nat => 0xa1880
| 133%nat => 0xa19e8
| 134%nat => 0xa1b70
| 135%nat => 0x21ba8
| 136%nat => 0x20c50
| 137%nat => 0xa1ccc
| 138%nat => 0x20d04
| 139%nat => 0x20d24
| 140%nat => 0x20d30
| 141%nat => 0x20d74
| 142%nat => 0x20da0
| 143%nat => 0x20e24
| 144%nat => 0x20e50
| 145%nat => 0x20e70
| 146%nat => 0x20e80
| 147%nat => 0x20e90
| 148%nat => 0x20ec8
| 149%nat => 0x20fe8
| 150%nat => 0x20ff4
| 151%nat => 0xa20d0
| 152%nat => 0xa22d4
| 153%nat => 0xa1984
| 154%nat => 0xa1f98
| 155%nat => 0xa2094
| 156%nat => 0xa216c
| 157%nat => 0xa23b8
| 158%nat => 0xa23bc
| 159%nat => 0x12418
| 160%nat => 0x8841c
| 161%nat => 0x2146c
| 162%nat => 0x214ac
| 163%nat => 0x214b0
| 164%nat => 0x214b4
| 165%nat => 0x214b8
| 166%nat => 0x214bc
| 167%nat => 0x2161c
| 168%nat => 0x21700
| 169%nat => 0x21718
| _ => 0
end.
Definition A_prog_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then A_prog_base else if (a <? A_HI 0)%nat then A_prog_obj (a - A_OBJ 0) else A_prog_hi (a - A_HI 0).
Lemma A_prog_val_range : forall a, 0 <= A_prog_val a < 2 ^ 64.
Proof.
intros a. unfold A_prog_val. destruct (Nat.eqb a A_TEXT); [unfold A_prog_base; zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold A_prog_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 15 (destruct m as [|m]; [zlit|]). zlit.
- unfold A_prog_hi. generalize (a - A_HI 0)%nat as m. intros m. do 170 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma A_prog_cert : pi_check asym (clookup A_prog_tbl) A_prog_val A_prog_sigma A_prog_listing = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma A_prog_obj_img : forall i, (i < 39)%nat -> IMG_LO <= A_prog_val (A_OBJ i) /\ A_prog_val (A_OBJ i) + 8 <= IMG_TOP.
Proof. intros i Hi. unfold IMG_LO, IMG_TOP. do 39 (destruct i as [|i]; [unfold A_prog_val, A_prog_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]). exfalso; lia.
Qed.
Lemma A_prog_obj0 : A_prog_val (A_OBJ 0) = 0xa2010.
Proof. vm_compute. reflexivity. Qed.
Lemma A_prog_obj1 : A_prog_val (A_OBJ 1) = 0xa2068.
Proof. vm_compute. reflexivity. Qed.
Lemma A_prog_obj12 : A_prog_val (A_OBJ 12) = 0xaaeb8.
Proof. vm_compute. reflexivity. Qed.
Lemma A_prog_got_uar_disj : (A_prog_val (A_OBJ 1) + 8 <= A_prog_val (A_OBJ 0) \/ A_prog_val (A_OBJ 0) + 8 <= A_prog_val (A_OBJ 1))
/\ (A_prog_val (A_OBJ 1) + 8 <= A_prog_val (A_OBJ 12) \/ A_prog_val (A_OBJ 12) + 8 <= A_prog_val (A_OBJ 1)).
Proof. unfold A_prog_val, A_prog_obj, A_OBJ, A_TEXT, A_HI. cbn. lia. Qed.
#[export] Instance PI_prog_A : PAImg A_prog_listing := {|
pa_segs := rsegs; pa_tbl := A_prog_tbl; pa_tbl_ok := A_prog_tbl_ok; pa_val := A_prog_val; pa_sigma := A_prog_sigma;
pa_cert := A_prog_cert; pa_B_ok := ltac:(unfold A_prog_val, A_prog_base; cbn; lia); pa_val_range := A_prog_val_range;
pa_wx := A_prog_wx; pa_segs_low := A_prog_segs_low; pa_lo := IMG_LO; pa_hi := IMG_TOP; pa_img_range := A_prog_range; pa_img_cover := A_prog_cover;
pa_obj_img := A_prog_obj_img; pa_relro_lo := A_prog_relro_lo; pa_relro_hi := A_prog_relro_hi; pa_relro_img := A_prog_relro |}.
Definition A_prog_slot (s : asym) : nat := Z.to_nat ((A_prog_sigma s - A_prog_base) / 4).
Lemma A_entry_LLVMFuzzerTestOneInput : A_prog_sigma AS_LLVMFuzzerTestOneInput = 0x815e0 /\ A_prog_slot AS_LLVMFuzzerTestOneInput = 0%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_check_no_overread : A_prog_sigma AS_check_no_overread = 0x81904 /\ A_prog_slot AS_check_no_overread = 201%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_parse_noting : A_prog_sigma AS_parse_noting = 0x81f14 /\ A_prog_slot AS_parse_noting = 589%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_check_bounded_alloc : A_prog_sigma AS_check_bounded_alloc = 0x81f8c /\ A_prog_slot AS_check_bounded_alloc = 619%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_check_as_written : A_prog_sigma AS_check_as_written = 0x81fb8 /\ A_prog_slot AS_check_as_written = 630%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_check_reject_clean : A_prog_sigma AS_check_reject_clean = 0x82110 /\ A_prog_slot AS_check_reject_clean = 716%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_check_reject_clean_starved : A_prog_sigma AS_check_reject_clean_starved = 0x82160 /\ A_prog_slot AS_check_reject_clean_starved = 736%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_read_members : A_prog_sigma AS_read_members = 0x825f8 /\ A_prog_slot AS_read_members = 1030%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_check_round_trip : A_prog_sigma AS_check_round_trip = 0x82870 /\ A_prog_slot AS_check_round_trip = 1188%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_same : A_prog_sigma AS_same = 0x82fb8 /\ A_prog_slot AS_same = 1654%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_ex_value : A_prog_sigma AS_ex_value = 0x832a4 /\ A_prog_slot AS_ex_value = 1841%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_ex_string : A_prog_sigma AS_ex_string = 0x84034 /\ A_prog_slot AS_ex_string = 2709%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_ex_word : A_prog_sigma AS_ex_word = 0x8452c /\ A_prog_slot AS_ex_word = 3027%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_ex_hex4 : A_prog_sigma AS_ex_hex4 = 0x84688 /\ A_prog_slot AS_ex_hex4 = 3114%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_ex_utf8 : A_prog_sigma AS_ex_utf8 = 0x84764 /\ A_prog_slot AS_ex_utf8 = 3169%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_round_trip_text : A_prog_sigma AS_round_trip_text = 0x8496c /\ A_prog_slot AS_round_trip_text = 3299%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_tx_put : A_prog_sigma AS_tx_put = 0x84cec /\ A_prog_slot AS_tx_put = 3523%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_tx_value : A_prog_sigma AS_tx_value = 0x84f04 /\ A_prog_slot AS_tx_value = 3657%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_tx_string : A_prog_sigma AS_tx_string = 0x852f4 /\ A_prog_slot AS_tx_string = 3909%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_tx_line : A_prog_sigma AS_tx_line = 0x85654 /\ A_prog_slot AS_tx_line = 4125%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_asan_module_ctor : A_prog_sigma AS_asan_module_ctor = 0x856c0 /\ A_prog_slot AS_asan_module_ctor = 4152%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_asan_module_dtor : A_prog_sigma AS_asan_module_dtor = 0x856f8 /\ A_prog_slot AS_asan_module_dtor = 4166%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_malloc : A_prog_sigma AS_fuzz_malloc = 0x85728 /\ A_prog_slot AS_fuzz_malloc = 4178%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_realloc : A_prog_sigma AS_fuzz_realloc = 0x858ac /\ A_prog_slot AS_fuzz_realloc = 4275%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_strdup : A_prog_sigma AS_fuzz_strdup = 0x85c28 /\ A_prog_slot AS_fuzz_strdup = 4498%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_free : A_prog_sigma AS_fuzz_free = 0x85c84 /\ A_prog_slot AS_fuzz_free = 4521%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_alloc_live : A_prog_sigma AS_fuzz_alloc_live = 0x85da0 /\ A_prog_slot AS_fuzz_alloc_live = 4592%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_alloc_peak : A_prog_sigma AS_fuzz_alloc_peak = 0x85dac /\ A_prog_slot AS_fuzz_alloc_peak = 4595%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_alloc_peak_reset : A_prog_sigma AS_fuzz_alloc_peak_reset = 0x85db8 /\ A_prog_slot AS_fuzz_alloc_peak_reset = 4598%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_alloc_count : A_prog_sigma AS_fuzz_alloc_count = 0x85dcc /\ A_prog_slot AS_fuzz_alloc_count = 4603%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_alloc_fail : A_prog_sigma AS_fuzz_alloc_fail = 0x85dd8 /\ A_prog_slot AS_fuzz_alloc_fail = 4606%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_alloc_ran_out : A_prog_sigma AS_fuzz_alloc_ran_out = 0x85dfc /\ A_prog_slot AS_fuzz_alloc_ran_out = 4615%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_alloc_ran_out_reset : A_prog_sigma AS_fuzz_alloc_ran_out_reset = 0x85e08 /\ A_prog_slot AS_fuzz_alloc_ran_out_reset = 4618%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_fuzz_alloc_most : A_prog_sigma AS_fuzz_alloc_most = 0x85e14 /\ A_prog_slot AS_fuzz_alloc_most = 4621%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_pj_parse : A_prog_sigma AS_pj_parse = 0x85e20 /\ A_prog_slot AS_pj_parse = 4624%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_parse_value : A_prog_sigma AS_parse_value = 0x85f10 /\ A_prog_slot AS_parse_value = 4684%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_pj_free : A_prog_sigma AS_pj_free = 0x864e4 /\ A_prog_slot AS_pj_free = 5057%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_pj_get : A_prog_sigma AS_pj_get = 0x86694 /\ A_prog_slot AS_pj_get = 5165%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_pj_get_str : A_prog_sigma AS_pj_get_str = 0x867dc /\ A_prog_slot AS_pj_get_str = 5247%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_pj_set : A_prog_sigma AS_pj_set = 0x8685c /\ A_prog_slot AS_pj_set = 5279%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_grow : A_prog_sigma AS_grow = 0x869bc /\ A_prog_slot AS_grow = 5367%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_pj_string : A_prog_sigma AS_pj_string = 0x86b58 /\ A_prog_slot AS_pj_string = 5470%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_pj_write : A_prog_sigma AS_pj_write = 0x86c10 /\ A_prog_slot AS_pj_write = 5516%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_write_value : A_prog_sigma AS_write_value = 0x86c8c /\ A_prog_slot AS_write_value = 5547%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_put : A_prog_sigma AS_put = 0x87094 /\ A_prog_slot AS_put = 5805%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_parse_items : A_prog_sigma AS_parse_items = 0x87298 /\ A_prog_slot AS_parse_items = 5934%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_parse_string : A_prog_sigma AS_parse_string = 0x8794c /\ A_prog_slot AS_parse_string = 6363%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_literal : A_prog_sigma AS_literal = 0x87f60 /\ A_prog_slot AS_literal = 6752%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_hex4 : A_prog_sigma AS_hex4 = 0x88088 /\ A_prog_slot AS_hex4 = 6826%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_put_utf8 : A_prog_sigma AS_put_utf8 = 0x88164 /\ A_prog_slot AS_put_utf8 = 6881%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_put_string : A_prog_sigma AS_put_string = 0x8836c /\ A_prog_slot AS_put_string = 7011%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry_indent : A_prog_sigma AS_indent = 0x886e0 /\ A_prog_slot AS_indent = 7232%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry___wrap_getenv : A_prog_sigma AS___wrap_getenv = 0x88750 /\ A_prog_slot AS___wrap_getenv = 7260%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_entry___wrap_getpid : A_prog_sigma AS___wrap_getpid = 0x88758 /\ A_prog_slot AS___wrap_getpid = 7262%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma A_alias_hints_ok : forall E, img_env A_prog_val A_LIM E -> alias_ok E A_alias_hints.
Proof.
intros E HE. unfold A_alias_hints.
repeat (split; [cbn [sv_denot]; rewrite !HE by (unfold A_TEXT, A_LIM, A_OBJ, A_HI; lia); f_equal; vm_compute; reflexivity|]).
exact I.
Qed.
End c.
