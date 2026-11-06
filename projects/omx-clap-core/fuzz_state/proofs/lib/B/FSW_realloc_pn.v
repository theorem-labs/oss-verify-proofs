(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf1.v, with its module paths and module names changed; 639 of its 687 lines of code are new or changed and 451 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_fuzz_free.v, with its module paths and module names changed; 744 of its 845 lines of code are new or changed and 586 lines of the source are left out. *)
(* fs ASan+UBSan (image B: fs.asan-ubsan), group ALLOC, a Theorem Labs lane: fuzz_realloc's p <> 0 arms (B 0x82bc4,
   alloc.c:75-94) and their segment interface, the B twin of lib/A/FSW_realloc_pn.v (same lemma names).
   proves function fuzz_realloc (B 0x82bc4) (reuse search: proof-index on main@f4cc67298b7 / ossv/recipes@5121fb8693b
   / ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb, by address on those four refs, and on named
   lane branches / `proof-index fuzz_realloc`, `git grep -i -e <addr>`, `git grep -E '^(Theorem|Lemma)
   .*fuzz_realloc_spec'`; B 0x82bc4: 0 hits, CONFIRM).

   MEASURED control flow (capstone 5.0.7 on the unstripped twin of the pinned fuzz_state.asan-ubsan; 103 words, no RVC):
   0x82bc4..0x82bd4 frame 32, save ra (sp0 - 8) / s0 (sp0 - 16) / s1 (sp0 - 24) / s2 (sp0 - 32); s0 = n 0x82bd8;
   `beqz a0` 0x82bdc:
   - p = 0: 0x82c14 a0 = s0, restore, tail `j fuzz_malloc` 0x82c2c.
   - p <> 0: GOT word 0x9fc10 -> s2 = the shadow base (0x82bf8); g_count := cnt + 1 (0x82c00); `bne cnt, fail` 0x82c04:
     - failing(): g_fail_at := -1 (0x82c0c), `j` 0x82d1c: a0 = 0, restore, `ret` 0x82d34.
     - otherwise: `bltu -17, n` 0x82c34 (taken iff n > 2^64 - 17: dead, n + HEAD < MALLOC_MAX); UBSan's p - 16 checks
       `beq p, 16` 0x82c3c and `bgeu 15, p` 0x82c44, both to `unimp` 0x82d38 (dead: p - 16 is a live block, >= 4096);
       s1 = p - 16, a1 = 16, `jal __asan_unpoison_memory_region` 0x82c54 (0x54aa4, ra 0x82c58); disown's two inline
       checks (lb shadow(s1) / bnez 0x82c64, lb shadow(s1 + 7) / bnez 0x82c78, both to the report arms 0x82d3c / 0x82d50);
       8 x lbu of the head and their reassembly into s2 = k (0x82c7c..0x82cd8); g_live -= k (0x82cdc / 0x82ce0);
       a1 = n + 16, a0 = s1, `jal __wrap_realloc` 0x82cec (0x530e8, ra 0x82cf0);
       `beqz a0` 0x82cf0: NULL (dead, FSW_realloc.arealloc_granted) -> 0x82d10 `jal own` (s1, k), a0 = 0, ret;
       non-NULL: a1 = s0 = n, restore, tail `j own` 0x82d0c (0x82acc) with a0 = b, a1 = n.
   Segments: SEG-AB (entry -> the realloc call point fsr_at_realloc, this file), SEG-CD (fsr_at_realloc -> arm (c):
   the realloc call, the resume, `beqz`, the tail call into own, lib/B/FSW_realloc_segCD.v).
   Port-from: lib/A/FSW_realloc_pn.v (this lane's A file), lib/B/FSW_fuzz_free.v (B's disown) and lib/B/FSW_fuzz_malloc.v
   (B's tail call into own). No rename. Relocated files: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG08 YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSpoisonS.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_ReallocModel FSW_K FSW_K3 FSW_ret FSW_rres FSW_statics FSW_statics_awr
FSW_head FSW_poison_conv FSW_fuzz_realloc_tbl FSW_realloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YB13.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================================================================================================================ *)
(* THE SEGMENT INTERFACE (frozen for SEG-AB, 2026-10-29). fuzz_realloc's real arm (p <> 0, cnt <> fail):            *)
(*   SEG-AB : entry -> fsr_at_realloc (the `jal __wrap_realloc` at 0x82cec, pc FS_AREALLOC_PC_B)                       *)
(*   SEG-CD : fsr_at_realloc -> fsr_post_c (arm (c) of fuzz_realloc_spec, journal k = 3)                               *)
(* ================================================================================================================ *)

(* the return addresses of the two runtime calls *)
Definition FSR_RA_UNPOISON : Z := 0x82c58.
Definition A_fuzz_realloc_raB : Z := 0x82cf0.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the journal footprint of arm (c) *)
Definition fsr_FPc (p k : Z) : list (Z * Z) := FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, k + HEAD)].

(* the entry's premises for the real arm (fuzz_realloc_spec's, at p <> 0 and cnt <> fail) *)
Definition fsr_pre_pn (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (p k n : Z) (old : list Z)
  (live peak cnt fail : Z) (U1 U2 : list (Z * Z)) : Prop :=
  fpreU tfibsegs B STK_fuzz_realloc ly S U W regs mem md ch /\ fs_heads B ly S U /\
  YK11.getr regs 10 = w64 p /\ YK11.getr regs 11 = w64 n /\ 1 <= n /\ n + HEAD < MALLOC_MAX /\
  fs_glob tfibsegs W mem live peak cnt fail /\ live + n < 2 ^ 64 /\ cnt + 1 < 2 ^ 64 /\ cnt <> fail /\
  p <> 0 /\ U = U1 ++ (p - HEAD, HEAD) :: U2 /\ fs_rblock tfibsegs B ly S W mem p k /\
  Z.of_nat (length old) = k /\ zbytes_at tfibsegs W mem p old /\ k <= live /\
  st_nev S + 3 <= EV_MAX /\ blocks_bytes S + (n + HEAD) <= LIVE_MAX.

(* the four words fuzz_realloc's prologue saved (0x82bc8..0x82bd4), at sp0 - 32 .. sp0 - 8: s2, s1, s0, ra *)
Definition fsr_frame_vals (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
  val_mem tfibsegs m (sp0 - 32) 8 (bv_unsigned (YK11.getr regs 18)) /\
  val_mem tfibsegs m (sp0 - 24) 8 (bv_unsigned (YK11.getr regs 9)) /\
  val_mem tfibsegs m (sp0 - 16) 8 (bv_unsigned (YK11.getr regs 8)) /\
  val_mem tfibsegs m (sp0 - 8) 8 (bv_unsigned (YK11.getr regs 1)).

(* the callee-saved registers fuzz_realloc never writes (s3..s11), gp and tp *)
Definition fsr_kept (regs regsT : bvmap 5 word) : Prop :=
  (forall r, 19 <= r <= 27 -> YK11.getr regsT (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
  YK11.getr regsT 3 = w64 (as_gp B) /\ YK11.getr regsT 4 = w64 (as_tp B).

(* the `jal __wrap_realloc` call point (pc FS_AREALLOC_PC_B = 0x530e8): disown done (the old head left U, g_live -= k),
   the journal still at the entry's layout and state (no block changed yet); s0 = n, s1 = p - HEAD, s2 = k *)
Definition fsr_at_realloc (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p k n : Z) (old : list Z) (live peak cnt fail : Z) (U1 U2 : list (Z * Z))
  (W2 : world tfibsegs) (c : config) : Prop :=
  exists regsT memT md2,
    c = mkCfg (mkst regsT (Z_to_bv 64 FS_AREALLOC_PC_B) memT (seg_rom tfibsegs)) md2 /\
    ajournal tfibsegs B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W (unpoison U mem) md []
      ly S W2 (unpoison (U1 ++ U2) memT) md2 0 /\
    ARU tfibsegs B ly S (U1 ++ U2) W2 memT md2 /\
    YK11.getr regsT 10 = w64 (p - HEAD) /\ YK11.getr regsT 11 = w64 (n + HEAD) /\
    YK11.getr regsT 1 = Z_to_bv 64 A_fuzz_realloc_raB /\ spZ regsT = spZ regs - 32 /\
    YK11.getr regsT 8 = w64 n /\ YK11.getr regsT 9 = w64 (p - HEAD) /\ YK11.getr regsT 18 = w64 k /\
    fsr_kept regs regsT /\
    fsr_frame_vals (mrestrict (w_H W2) memT) (spZ regs) regs /\
    fs_glob tfibsegs W2 memT (live - k) peak (cnt + 1) fail /\
    zbytes_at tfibsegs W2 memT p old.

(* arm (c) of fuzz_realloc_spec (journal k = 3), at the given U1 U2 *)
Definition fsr_post_c (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p k n : Z) (old : list Z) (live peak cnt fail : Z) (U1 U2 : list (Z * Z))
  : world tfibsegs -> config -> Prop :=
  fun W' c' => exists res,
    apost_baseU tfibsegs B STK_fuzz_realloc (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, k + HEAD)]) regs ly S W mem md 3 U
      (U1 ++ U2 ++ [(res - HEAD, HEAD)])
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
         (exists b1 b2 c1 c2, ablocks B ly S = b1 ++ (p - HEAD, k + HEAD) :: b2 /\
            ablocks B ly' S' = c1 ++ (res - HEAD, n + HEAD) :: c2 /\ c1 ++ c2 = b1 ++ b2) /\
         fs_heads B ly' S' (U1 ++ U2 ++ [(res - HEAD, HEAD)]) /\
         (0 < n -> fs_rblock tfibsegs B ly' S' W' mem' res n) /\
         zbytes_at tfibsegs W' mem' res (firstn (Z.to_nat (Z.min k n)) old) /\
         fs_glob tfibsegs W' mem' (live - k + n) (Z.max peak (live - k + n)) (cnt + 1) fail) W' c'.

(* SEG-AB: the entry, the branches (p <> 0, cnt <> fail, no overflow, UBSan's two p - 16 checks), the unpoison call
   (lib/B/FSW_poison_conv.fsw_unpoison16_atU), the resume at 0x82c58, disown's two checks (token run), the head load
   and g_live -= k, to the realloc call point *)
Definition fsr_segAB_stmt : Prop :=
  fs_img_facts tfibsegs B -> FsShadowSyms B -> aunpoison16_realizes tfibsegs B PC_unpoison ->
  forall ly S U W regs mem md ch p k n old live peak cnt fail U1 U2,
  fsr_pre_pn ly S U W regs mem md ch p k n old live peak cnt fail U1 U2 ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_realloc regs mem md)
    (fsr_at_realloc ly S U W regs mem md p k n old live peak cnt fail U1 U2).
End i.

(* the engine's form of the reassembled 8-byte head (B: 0x82c7c..0x82cd8; MEASURED, the same tree as A's 0x82ac0..0x82b1c), for the loaded value e *)
Definition fsr_rd8 (e : sv) : sv :=
  SAlu ALU_OR
    (SAlu ALU_SLL
       (SAlu ALU_OR
          (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL e (SLit 56))) (SLit 24))
                       (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL e (SLit 48))) (SLit 16)))
          (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL e (SLit 40))) (SLit 8))
                       (SExt false 8 (SAlu ALU_SRL e (SLit 32)))))
       (SLit 32))
    (SAlu ALU_OR
       (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL e (SLit 24))) (SLit 24))
                    (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL e (SLit 16))) (SLit 16)))
       (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL e (SLit 8))) (SLit 8))
                    (SExt false 8 e))).

Lemma fsr_tb_mod : forall a m i, 0 <= m -> Z.testbit (a mod 2 ^ m) i = (0 <=? i) && (i <? m) && Z.testbit a i.
Proof.
intros a m i Hm. destruct (Z.leb_spec 0 i) as [H0|H0].
- destruct (Z.ltb_spec i m) as [H|H].
  + rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  + rewrite Z.mod_pow2_bits_high by lia. reflexivity.
- rewrite !Z.testbit_neg_r by lia. reflexivity.
Qed.
Lemma fsr_tb_shl : forall a k i, 0 <= k -> Z.testbit (Z.shiftl a k) i = (k <=? i) && Z.testbit a (i - k).
Proof.
intros a k i Hk. destruct (Z.leb_spec 0 i) as [H0|H0].
- rewrite Z.shiftl_spec by lia. destruct (Z.leb_spec k i) as [H|H]; [reflexivity|].
  rewrite Z.testbit_neg_r by lia. reflexivity.
- rewrite !Z.testbit_neg_r by lia. destruct (Z.leb_spec k i); [lia | reflexivity].
Qed.
Lemma fsr_tb_shr : forall a k i, 0 <= k -> Z.testbit (Z.shiftr a k) i = (0 <=? i) && Z.testbit a (i + k).
Proof.
intros a k i Hk. destruct (Z.leb_spec 0 i) as [H0|H0].
- rewrite Z.shiftr_spec by lia. reflexivity.
- rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

(* bit-level identity tactic: the goal  X = v  where X is built from v by lor / shiftl / shiftr / mod 2^k / zcanon *)
Ltac fsr_bits_tac v :=
  unfold zcanon, M64; apply Z.bits_inj'; let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
  let Hvb := fresh "Hvb" in
  assert (Hvb : forall m, 64 <= m -> Z.testbit v m = false)
    by (intros ? ?; rewrite <- (Z.mod_small v (2 ^ 64)) by lia; rewrite Z.mod_pow2_bits_high by lia; reflexivity);
  repeat first
    [ rewrite fsr_tb_mod by lia
    | rewrite Z.lor_spec
    | rewrite fsr_tb_shr by lia
    | rewrite fsr_tb_shl by lia ];
  let Hc := fresh "Hc" in
  assert (n < 8 \/ 8 <= n < 16 \/ 16 <= n < 24 \/ 24 <= n < 32 \/ 32 <= n < 40 \/ 40 <= n < 48 \/ 48 <= n < 56 \/
          56 <= n < 64 \/ 64 <= n) as Hc by lia;
  repeat (destruct Hc as [Hc|Hc]);
  repeat match goal with
    | |- context [?x <=? ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia ]
    | |- context [?x <? ?y] =>
        first [ rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia ]
    end; cbn [andb orb];
  repeat match goal with |- context [Z.testbit v ?i] =>
    lazymatch i with n => fail | _ => replace i with n by lia end end;
  first [ (destruct (Z.testbit v n); reflexivity) | (rewrite Hvb by lia; reflexivity) ].

(* the reassembled head is the head's value *)
Lemma fsr_rd8_denot : forall E e, sv_denot E (fsr_rd8 e) = sv_denot E e.
Proof.
intros E e. apply U_inj. unfold fsr_rd8.
rewrite !U_SAlu, !U_zext, !U_SAlu, !U_lit by lia. cbn [zalu_raw Z.of_N].
change (Z.land 24 63) with 24. change (Z.land 16 63) with 16. change (Z.land 8 63) with 8. change (Z.land 32 63) with 32.
change (Z.land 56 63) with 56. change (Z.land 48 63) with 48. change (Z.land 40 63) with 40.
pose proof (U_range E e) as Hr. unfold M64 in Hr.
set (v := U E e) in *. fsr_bits_tac v.
Qed.


(* ---------------------------------------------------------------------------------------------------------------- *)
(* awr_ok plumbing: a run's start memory has the entry's (or the resume's) skeleton; a resume with extra regions      *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma fsr_awr_skel : forall E rs rs' STK sp0 FP bl0 blc ly own fr0,
  awr_ok tfibsegs B E rs STK sp0 FP bl0 blc ly own fr0 -> skeleton rs' = skeleton rs ->
  awr_ok tfibsegs B E rs' STK sp0 FP bl0 blc ly own fr0.
Proof.
intros E rs rs' STK sp0 FP bl0 blc ly own fr0 H Hsk a Ha. apply H. exact (in_wrange_skeleton E rs' rs a Hsk Ha).
Qed.

Lemma fsr_awr_app : forall E rs1 rs2 STK sp0 FP bl0 blc ly own fr0,
  awr_ok tfibsegs B E rs1 STK sp0 FP bl0 blc ly own fr0 -> awr_ok tfibsegs B E rs2 STK sp0 FP bl0 blc ly own fr0 ->
  awr_ok tfibsegs B E (rs1 ++ rs2) STK sp0 FP bl0 blc ly own fr0.
Proof.
intros E rs1 rs2 STK sp0 FP bl0 blc ly own fr0 H1 H2 a (r & Hr & Ha).
apply in_app_or in Hr as [Hr|Hr]; [apply H1 | apply H2]; exists r; split; assumption.
Qed.

Lemma fsr_pstat_FPc : forall p k a, inFP FS_PSTAT_FP a -> inFP (fsr_FPc p k) a.
Proof.
intros p k a (r & Hr & Ha). exists r. split; [unfold fsr_FPc; apply in_or_app; left; exact Hr | exact Ha].
Qed.

Hypothesis IMG : fs_img_facts tfibsegs B.

(* every run from the entry (or a branch of it) writes the entry state's windows *)
Lemma fsr_awr_entry : forall E rs STK sp0 FP bl0 blc ly own fr0,
  bv_unsigned (ew E 2) = sp0 -> 32 <= STK -> (forall a, inFP FS_PSTAT_FP a -> inFP FP a) ->
  skeleton rs = skeleton (ss_mem (fss0TS A_fuzz_realloc 32)) ->
  awr_ok tfibsegs B E rs STK sp0 FP bl0 blc ly own fr0.
Proof.
intros E rs STK sp0 FP bl0 blc ly own fr0 E2 HS HFP Hsk.
exact (fsr_awr_skel E _ rs STK sp0 FP bl0 blc ly own fr0
  (fsw_awr_TS B IMG E A_fuzz_realloc 32 STK sp0 FP bl0 blc ly own fr0 E2 ltac:(lia) HFP) Hsk).
Qed.
End a.

Ltac fsr_awr_entry_tac B IMG Usp HFP :=
  lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ =>
    apply (fsr_awr_entry B IMG);
    first
      [ solve [exact Usp]
      | solve [exact HFP]
      | solve [lazymatch goal with |- 32 <= STK_fuzz_realloc => apply Z.leb_le; vm_compute; reflexivity end]
      | solve [lazymatch goal with |- skeleton _ = _ => vm_compute; reflexivity end] ]
  end.


(* ---------------------------------------------------------------------------------------------------------------- *)
(* Bytes kept over a range across runs and calls; the walk's resumed states                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the bytes [lo, hi) read the same on m and m' *)
Definition fsr_KB (H : word -> bool) (m m' : word -> option byte) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.

Lemma fsr_KB_refl : forall H m lo hi, fsr_KB H m m lo hi.
Proof. intros H m lo hi a _. reflexivity. Qed.

Lemma fsr_KB_trans : forall H m1 m2 m3 lo hi, fsr_KB H m1 m2 lo hi -> fsr_KB H m2 m3 lo hi -> fsr_KB H m1 m3 lo hi.
Proof. intros H m1 m2 m3 lo hi K1 K2 a Ha. rewrite (K2 a Ha). exact (K1 a Ha). Qed.

(* a run keeps the bytes no region of its start state writes *)
Lemma fsr_KB_run : forall E rs (H : word -> bool) m m' lo hi,
  frame_of E rs m m' -> 0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> ~ in_wrange E rs a) -> fsr_KB H m m' lo hi.
Proof.
intros E rs H m m' lo hi HF Hlo Hhi Hn a Ha.
apply (mbyte_of_aview tfibsegs). apply (aview_at tfibsegs). apply HF. rewrite (wz a ltac:(lia)). exact (Hn a Ha).
Qed.

(* a call's unpoisoned frame keeps application bytes (unpoison is the identity there) *)
Lemma fsr_KB_unpoison : forall ly S U U' (W : world tfibsegs) m m' md md' lo hi,
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly S U' W m' md' -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  (forall a, lo <= a < hi -> aview tfibsegs (w_H W) (unpoison U' m') a = aview tfibsegs (w_H W) (unpoison U m) a) ->
  fsr_KB (w_H W) m m' lo hi.
Proof.
intros ly S U U' W m m' md md' lo hi HA HA' Hlo Hhi Happ Hv a Ha.
apply (mbyte_of_aview tfibsegs).
rewrite <- (aview_at tfibsegs (w_H W) (unpoison U' m') m' a
  (fs_head_app_view B ly S U' W m' md' a HA' ltac:(lia) (Happ a Ha))).
rewrite <- (aview_at tfibsegs (w_H W) (unpoison U m) m a
  (fs_head_app_view B ly S U W m md a HA ltac:(lia) (Happ a Ha))).
exact (Hv a Ha).
Qed.

Lemma fsr_val_mem_KB : forall H m m' a (n : nat) v lo hi, fsr_KB H m m' lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v lo hi K H1 H2 Hv i Hi. rewrite (K (a + Z.of_nat i) ltac:(lia)). exact (Hv i Hi). Qed.

Lemma fsr_garr8_KB : forall H m m' p l lo hi, fsr_KB H m m' lo hi -> lo <= p -> p + Z.of_nat (length l) <= hi ->
  garr8 tfibsegs (mrestrict H m) p l -> garr8 tfibsegs (mrestrict H m') p l.
Proof.
intros H m m' p l lo hi K H1 H2 G j Hj. destruct (G j Hj) as [Hv Hr]. split; [|exact Hr].
apply (fsr_val_mem_KB H m m' _ 1 _ lo hi K); [lia | lia | exact Hv].
Qed.

(* fs_glob from the statics' bytes *)
Lemma fsr_glob_KB : forall (W : world tfibsegs) m m' live peak cnt fail,
  fs_glob tfibsegs W m live peak cnt fail ->
  (forall a, inFP FS_PSTAT_FP a -> mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail (G1 & G2 & G3 & G4 & GR) He.
assert (V : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv i Hi. rewrite He; [exact (Hv i Hi)|]. apply (inFP_FS_PSTAT_FP g Hg). lia. }
split; [apply (V G_LIVE); [vm_compute; tauto | exact G1]|].
split; [apply (V G_PEAK); [vm_compute; tauto | exact G2]|].
split; [apply (V G_COUNT); [vm_compute; tauto | exact G3]|].
split; [apply (V G_FAIL); [vm_compute; tauto | exact G4]|].
exact GR.
Qed.

(* the statics lie below the shadow, inside fs.asan-ubsan's RW window *)
Lemma fsr_pstat_low : forall a, inFP FS_PSTAT_FP a -> 0x9f000 <= a < 0x5fd000.
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Ha; lia|]).
destruct Hr.
Qed.

(* a value chunk read under one env and base is the same chunk under another env and base when the absolute address
   and the value agree (as a Theorem Labs lane's fm_chunk_move) *)
Lemma fsr_chunk_move : forall E E' m base base' off off' sz e e',
  base + off = base' + off' -> sv_denot E e = sv_denot E' e' ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal sz e)) ->
  YP09.chunk_ok tfibsegs E' m base' (YP09.mkChunk off' (CVal sz e')).
Proof.
intros E E' m base base' off off' sz e e' Hb He H i Hi. destruct (H i Hi) as (b & H1 & H2). exists b.
cbn [cbyte YP09.c_off YP09.c_val] in *. rewrite <- He, <- Hb. split; [exact H1 | exact H2].
Qed.

(* FSW_statics.fs_pstat_regions_ok under an env with further atoms after the statics' *)
Lemma fsr_pstat_ok : forall (W : world tfibsegs) regs mem live peak cnt fail ys,
  fs_glob tfibsegs W mem live peak cnt fail ->
  Forall (region_ok tfibsegs (Ereg regs (fs_extraTS cnt fail live peak ++ ys)) (mrestrict (w_H W) mem)) fs_pstat_regions.
Proof.
intros W regs mem live peak cnt fail ys GL.
pose proof GL as (G1 & G2 & G3 & G4 & GR).
set (E := Ereg regs (fs_extraTS cnt fail live peak ++ ys)).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite ew_Ereg_extra; apply app_nth1; cbn; lia).
assert (RS : forall g (j : nat) v, (1 <= j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> 0x9f000 <= g -> g + 8 <= 0x5fd000 -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  region_ok tfibsegs E (mrestrict (w_H W) mem) (fs_pstat_region g (32 + j))).
{ intros g j v Hj Hv Hr Hg1 Hg2 Hm.
  unfold region_ok, fs_pstat_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. unfold writable_at. apply YB13.tfib_rw_window. rewrite unsigned_lit_small by lia. lia.
  - constructor; [|constructor].
    exact (chunk_ok_val tfibsegs _ _ 0 g 8 (SOff (32 + j) 0) v
      ltac:(rewrite fsw_SOff0; etransitivity; [exact (EX j ltac:(lia)) | exact Hv]) ltac:(cbn [Z.of_N]; lia)
      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Hm)). }
unfold fs_pstat_regions, xatom.
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- apply (RS G_COUNT 1%nat cnt); first [solve [lia] | solve [reflexivity] | solve [unfold G_COUNT; lia] | solve [exact G3]].
- apply (RS G_FAIL 2%nat fail); first [solve [lia] | solve [reflexivity] | solve [unfold G_FAIL; lia] | solve [exact G4]].
- apply (RS G_LIVE 3%nat live); first [solve [lia] | solve [reflexivity] | solve [unfold G_LIVE; lia] | solve [exact G1]].
- apply (RS G_PEAK 4%nat peak); first [solve [lia] | solve [reflexivity] | solve [unfold G_PEAK; lia] | solve [exact G2]].
Qed.

(* the GOT word 0x9fc10 and the shadow cell 0xa8438 of fs.asan-ubsan are image bytes (FSW_statics.fs_pstat_img's method) *)
Lemma fsr_cells_img : forall a, inFP [(0x9fc10, 0x9fc18); (0xa8438, 0xa8440)] a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
    (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) [(0x9fc10, 0x9fc18); (0xa8438, 0xa8440)] = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. cbv beta in H.
apply existsb_exists in H as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

Hypothesis IMG : fs_img_facts tfibsegs B.

(* a resumed state with the statics and a read-only head region writes what fss_retT with the statics writes *)
Lemma fsr_awr_retH : forall E (r f STK sp0 : Z) cs gf (m : nat) hc FP bl0 blc ly own fr0,
  bv_unsigned (ew E 2) = sp0 - f -> 0 <= f <= STK -> (forall a, inFP FS_PSTAT_FP a -> inFP FP a) ->
  awr_ok tfibsegs B E (ss_mem (fss_retT r f cs (fs_pstat_regions ++ [fs_head_region m 0 hc]) gf)) STK sp0 FP bl0 blc ly
    own fr0.
Proof.
intros E r f STK sp0 cs gf m hc FP bl0 blc ly own fr0 Hsp Hf HFP a (rg & Hin & Ha).
unfold fss_retT, fsT_ret_regions in Hin. cbn [ss_mem] in Hin.
rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin|[<-|[]]].
- apply (fsw_awr_retTS B IMG E r f STK sp0 cs gf FP bl0 blc ly own fr0 Hsp Hf HFP).
  exists rg. split; [|exact Ha]. unfold fss_retT, fsT_ret_regions. cbn [ss_mem]. exact Hin.
- exfalso. cbn [fs_head_region YP09.r_wlo YP09.r_whi] in Ha. lia.
Qed.

Lemma fsr_val_of_chunk8 : forall E m base off e v a,
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  a = base + off -> val_mem tfibsegs m a 8 v.
Proof.
intros E m base off e v a Hc He Hv ->.
exact (val_of_chunk_ok tfibsegs E m base off 8 e v Hc He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv)
  ltac:(cbn; lia)).
Qed.
End k.

(* the frame chunks of the state resumed after disown's unpoison (B: fuzz_realloc's four saved words at [sp0 - 32, sp0):
   s2, s1, s0, ra, as xatoms 4..7 = atoms 37..40, written in the order sd ra 0x18 / s0 0x10 / s1 8 / s2 0, so the chunk at
   offset 0 is s2 = atom 40 .. offset 24 is ra = atom 37; the same layout as lib/B/FSW_fuzz_free.v's ff_cs) and the old
   head's value (xatom 8 = atom 41), held in the head region based at atom 9 (s1 = p - HEAD) *)
Definition fsr_cs : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff 40 0)); YP09.mkChunk 8 (CVal 8 (SOff 39 0));
   YP09.mkChunk 16 (CVal 8 (SOff 38 0)); YP09.mkChunk 24 (CVal 8 (SOff 37 0))].
Definition fsr_rsB : list YP09.region :=
  fs_pstat_regions ++ [fs_head_region 9 0 [YP09.mkChunk 0 (CVal 8 (SOff 41 0))]].
Definition fsr_gfB : list (nat * afact) :=
  [(9%nat, mkAF 4096 (2 ^ 47 - 16) 4); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition fsr_xsB (regs : bvmap 5 word) (k cnt fail live peak : Z) : list word :=
  fs_pstat_xs (cnt + 1) fail live peak ++ [getr regs 1; getr regs 8; getr regs 9; getr regs 18] ++ [Z_to_bv 64 k].

(* the write windows of fuzz_realloc's entry state and of the state resumed after disown's unpoison: the frame, the
   statics; the cells and the head are read-only *)
Lemma fsr_nw_entry : forall E rs a, skeleton rs = skeleton (ss_mem (fss0TS A_fuzz_realloc 32)) ->
  a < bv_unsigned (ew E 2) - 32 -> ~ inFP FS_PSTAT_FP a -> ~ in_wrange E rs a.
Proof.
intros E rs a Hsk Hlt Hnf Hw. apply (in_wrange_skeleton E rs _ a Hsk) in Hw. destruct Hw as (r & Hin & Ha).
assert (NS : forall g, In (g, g + 8) FS_PSTAT_FP -> ~ (g <= a < g + 8))
  by (intros g Hg Ha'; apply Hnf; exists (g, g + 8); split; [exact Hg | cbn [fst snd]; lia]).
vm_compute in Hin.
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    first [ lia
          | lazymatch type of Ha with _ + ?g <= _ < _ => apply (NS g); [vm_compute; tauto | lia] end ]
  | ]).
destruct Hin.
Qed.

Lemma fsr_nw_ret : forall E rs a r, skeleton rs = skeleton (ss_mem (fss_retT r 32 fsr_cs fsr_rsB fsr_gfB)) ->
  a < bv_unsigned (ew E 2) -> ~ inFP FS_PSTAT_FP a -> ~ in_wrange E rs a.
Proof.
intros E rs a r Hsk Hlt Hnf Hw. apply (in_wrange_skeleton E rs _ a Hsk) in Hw. destruct Hw as (rg & Hin & Ha).
assert (NS : forall g, In (g, g + 8) FS_PSTAT_FP -> ~ (g <= a < g + 8))
  by (intros g Hg Ha'; apply Hnf; exists (g, g + 8); split; [exact Hg | cbn [fst snd]; lia]).
vm_compute in Hin.
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    first [ lia
          | lazymatch type of Ha with _ + ?g <= _ < _ => apply (NS g); [vm_compute; tauto | lia] end ]
  | ]).
destruct Hin.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* SEG-A + SEG-B: the real arm from the entry through disown (unpoison the old head, its two checks, the head load,    *)
(* g_live -= k) to the `jal __wrap_realloc` call point fsr_at_realloc                                                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Ltac fsr_kb_tac HF W NWB Klo Khi K :=
  lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
    let Hsk := fresh "Hsk" in
    assert (Hsk : skeleton rs = skeleton (ss_mem (fss0TS A_fuzz_realloc 32)))
      by (lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end);
    pose proof (fsr_KB_run E rs (w_H W) m m' _ _ HF Klo Khi (NWB rs Hsk)) as K; clear Hsk
  end.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* SEG-0 + SEG-F: p <> 0 and failing() (alloc.c:79): g_count = cnt + 1, g_fail_at = SIZE_MAX, NULL, no allocation  *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* fs's image facts (lib/B/FSH_Rt.fs_img_facts) and the shadow-base cells of TfibB (lib/B/FSH_Base.FsShadowSyms: GOT
   word 0x9fc10 -> cell 0xa8438); owner RELOC-B / the B start-up layer *)
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis SHS : FsShadowSyms B.
Let FS_GOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 SHS.
Let FS_CELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 SHS.

Lemma fsr_pn0_fail : forall ly S U (W : world tfibsegs) regs mem md ch p k n old live peak cnt fail,
  fpreU tfibsegs B STK_fuzz_realloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  YK11.getr regs 10 = w64 p -> 0 < p < 2 ^ 64 ->
  cnt = fail -> fs_glob tfibsegs W mem live peak cnt fail -> cnt + 1 < 2 ^ 64 ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_realloc regs mem md)
    (fsr_post B regs ly S U W mem md p k n old live peak cnt fail).
Proof.
intros ly S U W regs mem md ch p k n old live peak cnt fail HPRE FH H10 Hp Hcf HGL Hcn.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_realloc ly S U W regs mem md ch HAP) as HARU.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_fuzz_realloc ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FR : STK_fuzz_realloc = ltac:(let v := eval vm_compute in STK_fuzz_realloc in exact v)) by reflexivity.
pose proof HGL as (G1 & G2 & G3 & G4 & GR).
pose proof (fsw_entryTS B STK_fuzz_realloc 32 ly S U W regs mem md ch A_fuzz_realloc live peak cnt fail FS_GOT FS_CELL
  HAP ltac:(rewrite FR; lia) ltac:(vm_compute; reflexivity) HGL) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_realloc FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAN) as HJ.
set (E := Ereg regs (fs_extraTS cnt fail live peak)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E33 : ew E 33 = Z_to_bv 64 cnt) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 fail) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 live) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 peak) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (HFP : forall x, inFP FS_PSTAT_FP x -> inFP FS_PSTAT_FP x) by (intros x Hx; exact Hx).
unfold cfg_at. change (w64 A_fuzz_realloc) with (Z_to_bv 64 A_fuzz_realloc).
(* 0x82bc4..0x82bd8: frame, saves, s0 = n; stops at beqz a0 0x82bdc *)
fsw_aj_runU fsr_tbl_ok HS HJ HARU.
{ fsr_awr_entry_tac B IMG Usp HFP. }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS).
1: { intros Hb _. exfalso. rewrite branch_eq_U, (U_atom E 10 p E10 ltac:(lia)), U_lit in Hb by lia.
     apply Z.eqb_eq in Hb. lia. }
intros _ HS2. clear HS.
(* 0x82be0..0x82c00: the GOT / cnt / fail / shadow-base loads, g_count = cnt + 1; stops at bne cnt, fail 0x82c04 *)
fsw_aj_runU fsr_tbl_ok HS2 HJ HARU.
{ fsr_awr_entry_tac B IMG Usp HFP. }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 33 0) (b := SOff 34 0) (1 := HS2).
1: { intros Hb _. exfalso. rewrite branch_ne_U, (U_atom E 33 cnt E33 ltac:(lia)), (U_atom E 34 fail E34 ltac:(lia)) in Hb.
     rewrite Hcf, Z.eqb_refl in Hb. discriminate Hb. }
intros _ HS3. clear HS2.
(* 0x82c08..0x82c10, 0x82d1c..0x82d30: g_fail_at = SIZE_MAX, a0 = 0, the epilogue; stops at ret 0x82d34 *)
fsw_aj_runU fsr_tbl_ok HS3 HJ HARU.
{ fsr_awr_entry_tac B IMG Usp HFP. }
pose proof (fsw_reg_atom (w_H W) regs _ _ ms1 1%bv 1%bv 1 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R1.
pose proof (fsw_reg_lit (w_H W) E _ ms1 10%bv 0 HS3 ltac:(vm_compute; reflexivity) ltac:(lia)) as R10.
pose proof (st_ok_mem_ok tfibsegs E _ _ HS3) as HM. cbn [restrict ms_mem] in HM.
set (Qa := fun ly' S' (W' : world tfibsegs) regs' mem' (md' : Model) =>
  getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\ fs_heads B ly' S' U /\
  fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ).
assert (HQa : forall md', Qa ly S W (ms_regs ms1) (ms_mem ms1) md').
{ intros md'. subst Qa. cbv beta. split; [rewrite R10; reflexivity|]. split; [reflexivity|]. split; [exact FH|].
  apply (fs_glob_of_TS E W (ms_mem ms1) _ live peak (cnt + 1) SIZE_MAXZ (SOff 35 0) (SOff 36 0) (SOff 33 1)
    (SLit 18446744073709551615) HM).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; first [exact E35 | exact E36]]
    | solve [rewrite denot_lit_U, U_SOff, E33, unsigned_lit_small by lia; rewrite zcanon_id by (unfold M64; lia);
             reflexivity]
    | solve [rewrite denot_lit_U, U_lit by lia; reflexivity]
    | solve [unfold SIZE_MAXZ; lia] ]. }
assert (HPa : aregs_preserved regs (ms_regs ms1)).
{ eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs (fs_extraTS cnt fail live peak) HS3).
  all: first [ solve [apply env_agree_refl]
             | solve [lazymatch goal with |- forallb _ _ = true => vm_compute; reflexivity end] ]. }
assert (Hjr : v_jalr (getr (ms_regs ms1) 1) 0 = getr regs 1) by (rewrite R1; exact Hra).
eapply SRr_mono.
{ exact (fsw_retU B fsr_tbl fsr_tbl_ok W E _ ms1 _ STK_fuzz_realloc (spZ regs) FS_PSTAT_FP regs ly S U W mem md ly S U 0
    Qa HS3 eq_refl ltac:(vm_compute; reflexivity) Hjr HJ HARU HPa (fun mat => HQa _)). }
intros W' c' _ HP'. unfold fsr_post. left. split; [exact Hcf | exact HP'].
Qed.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* SEG-A + SEG-B: the real arm from the entry through disown (unpoison the old head, its two checks, the head load,    *)
(* g_live -= k) to the `jal __wrap_realloc` call point fsr_at_realloc (B: 0x82cec -> 0x530e8)                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma fsr_segAB : fsr_segAB_stmt B.
Proof.
intros IMG SHS UPO ly S U W regs mem md ch p k n old live peak cnt fail U1 U2
  (HPRE & FH & H10 & H11 & Hn1 & Hn2 & HGL & Hlv & Hcn & Hcf & Hp0 & EU & HRB & Hlen & HZB & Hkl & Hev & Hbb).
pose proof (proj1 SHS) as FS_GOT. pose proof (proj2 SHS) as FS_CELL.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_realloc ly S U W regs mem md ch HAP) as HARU.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_fuzz_realloc ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HGL as (G1 & G2 & G3 & G4 & Hlp & Hp64 & Hc64 & Hf64).
assert (FR : STK_fuzz_realloc = ltac:(let v := eval vm_compute in STK_fuzz_realloc in exact v)) by reflexivity.
assert (Hn64 : 0 <= n < 2 ^ 64) by (unfold MALLOC_MAX, HEAD in *; lia).
pose proof HRB as (Hblk & Hp16 & Hk0 & Hhead).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) HAR Hblk)
  as (Hb16 & Hb4096 & Hbceil & Happ & _).
assert (Hceil47 : alloc_ceiling < 2 ^ 47) by exact alloc_ceiling_lt.
assert (Hrqk : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hrqk in Hbceil.
assert (Hp64' : 0 < p < 2 ^ 64) by (unfold HEAD in *; lia).
rewrite FR in Hceil.
assert (Hblkr : forall a, p - HEAD <= a < p + k -> a + 128 < spZ regs - 32) by (intros a Ha; unfold HEAD in *; lia).
assert (NIMG : forall a, p - HEAD <= a < p + k -> ~ inFP FS_PSTAT_FP a).
{ intros a Ha Hf. exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) a HAR Hblk
    ltac:(rewrite Hrqk; unfold HEAD in *; lia) (fs_pstat_img a Hf)). }
assert (HAPPB : forall a, p - HEAD <= a < p + k -> a < SHADOW_OFF \/ kHighMemBeg <= a).
{ intros a Ha. destruct (in_app_addr _ _ a Happ ltac:(rewrite Hrqk; unfold HEAD in *; lia)) as [_ [Hx|[Hx _]]].
  - left. unfold kLowShadowBeg, SHADOW_OFF in *. lia.
  - right. exact Hx. }
assert (Klo : 0 <= p - HEAD) by (clear - Hb4096; lia).
assert (Khi : p + k <= 2 ^ 64) by (clear - Hbceil Hceil47; unfold HEAD in *; lia).
assert (F32 : 0 < 32 /\ 32 <= STK_fuzz_realloc) by (rewrite FR; lia).
assert (Hcsr : Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 32) fsr_cs)
  by (unfold fsr_cs; repeat constructor; cbn; lia).
assert (Hh8 : (p - HEAD) mod 8 = 0).
{ pose proof Hb16 as Hq16. apply Z.mod_divide in Hq16 as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 16) with ((2 * q) * 8) by ring. apply Z.mod_mul. lia. }
assert (Happh : in_app (p - HEAD) 16)
  by (apply (in_app_sub _ _ (p - HEAD) 16 Happ); rewrite ?Hrqk; unfold HEAD in *; lia).
assert (Hk64 : 0 <= k < 2 ^ 64) by (clear - Hk0 Hkl Hlp Hp64; lia).
assert (Hh64 : 0 <= p - HEAD + 0 < 2 ^ 64) by (clear - Hb4096 Hp64'; unfold HEAD in *; lia).
assert (Hn16 : 0 <= n + 16 < 2 ^ 64) by (clear - Hn1 Hn2; unfold MALLOC_MAX, HEAD in *; lia).
assert (Hn0 : 0 <= n + 0 < 2 ^ 64) by (clear - Hn64; lia).
assert (Hsp0 : 0 <= spZ regs - 32 + 0 < 2 ^ 64) by (clear - Hceil H47 C1; lia).
assert (Hlk : 0 <= live - k <= peak) by (clear - Hk0 Hkl Hlp; lia).
assert (Hlk64 : 0 <= live - k < 2 ^ 64) by (clear - Hk0 Hkl Hlp Hp64; lia).
assert (Hlv64 : 0 <= live < 2 ^ 64) by (clear - Hlp Hp64; lia).
assert (Hc1 : 0 <= cnt + 1 < 2 ^ 64) by (clear - Hc64 Hcn; lia).
pose proof (fsw_entryTS B STK_fuzz_realloc 32 ly S U W regs mem md ch A_fuzz_realloc live peak cnt fail FS_GOT FS_CELL
  HAP ltac:(rewrite FR; lia) ltac:(vm_compute; reflexivity) HGL) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_realloc (fsr_FPc p k) ly S W regs (unpoison U mem) md ch HAN) as HJ.
set (E := Ereg regs (fs_extraTS cnt fail live peak)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cnt) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 fail) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 live) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 peak) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (HFP : forall x, inFP FS_PSTAT_FP x -> inFP (fsr_FPc p k) x) by exact (fsr_pstat_FPc p k).
assert (NWB : forall rs, skeleton rs = skeleton (ss_mem (fss0TS A_fuzz_realloc 32)) ->
  forall a, p - HEAD <= a < p + k -> ~ in_wrange E rs a).
{ intros rs Hsk a Ha. apply (fsr_nw_entry E rs a Hsk); [rewrite Usp; pose proof (Hblkr a Ha); lia | exact (NIMG a Ha)]. }
unfold cfg_at. change (w64 A_fuzz_realloc) with (Z_to_bv 64 A_fuzz_realloc).
(* 0x82bc4..0x82bd8: frame, saves, s0 = n; stops at beqz a0 0x82bdc *)
fsw_aj_runU fsr_tbl_ok HS HJ HARU.
{ fsr_awr_entry_tac B IMG Usp HFP. }
fsr_kb_tac HF W NWB Klo Khi K1.
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS).
1: { intros Hb _. exfalso. rewrite branch_eq_U, (U_atom E 10 p E10 ltac:(lia)), U_lit in Hb by lia.
     apply Z.eqb_eq in Hb. lia. }
intros _ HS2. clear HS.
(* 0x82be0..0x82c00: GOT / cnt / fail / shadow-base loads, g_count = cnt + 1; stops at bne cnt, fail 0x82c04 *)
fsw_aj_runU fsr_tbl_ok HS2 HJ HARU.
{ fsr_awr_entry_tac B IMG Usp HFP. }
fsr_kb_tac HF W NWB Klo Khi K2.
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 33 0) (b := SOff 34 0) (1 := HS2).
2: { intros Hb _. exfalso. rewrite branch_ne_U, (U_atom E 33 cnt E33 Hc64), (U_atom E 34 fail E34 Hf64) in Hb.
     apply negb_false_iff, Z.eqb_eq in Hb. exact (Hcf Hb). }
intros _ HS3. clear HS2.
(* 0x82c30: a1 = -17; stops at bltu a1, s0 0x82c34 (taken iff n > 2^64 - 17: refuted) *)
fsw_aj_runU fsr_tbl_ok HS3 HJ HARU.
{ fsr_awr_entry_tac B IMG Usp HFP. }
fsr_kb_tac HF W NWB Klo Khi K3.
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_LTU) (a := SLit 18446744073709551599) (b := SOff 11 0) (1 := HS3).
1: { intros Hb _. exfalso. rewrite branch_ltu_U, (U_lit E 18446744073709551599 ltac:(lia)), (U_atom E 11 n E11 Hn64) in Hb.
     apply Z.ltb_lt in Hb. unfold MALLOC_MAX, HEAD in *. lia. }
intros _ HS4. clear HS3.
(* 0x82c38: a1 = 16; stops at beq a0, a1 0x82c3c, UBSan's p - 16 check edge 1 (taken iff p = 16: refuted, 4096 <= p - 16) *)
fsw_aj_runU fsr_tbl_ok HS4 HJ HARU.
{ fsr_awr_entry_tac B IMG Usp HFP. }
fsr_kb_tac HF W NWB Klo Khi K4.
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 16) (1 := HS4).
1: { intros Hb _. exfalso. rewrite branch_eq_U, (U_atom E 10 p E10 ltac:(lia)), U_lit in Hb by lia.
     apply Z.eqb_eq in Hb. unfold HEAD in *. lia. }
intros _ HS5. clear HS4.
(* 0x82c40: a1 = 15; stops at bgeu a1, a0 0x82c44, edge 2 (taken iff p <= 15: refuted the same way) *)
fsw_aj_runU fsr_tbl_ok HS5 HJ HARU.
{ fsr_awr_entry_tac B IMG Usp HFP. }
fsr_kb_tac HF W NWB Klo Khi K5.
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_GEU) (a := SLit 15) (b := SOff 10 0) (1 := HS5).
1: { intros Hb _. exfalso. rewrite branch_geu_U, (U_atom E 10 p E10 ltac:(lia)), U_lit in Hb by lia.
     apply negb_true_iff, Z.ltb_ge in Hb. unfold HEAD in *. lia. }
intros _ HS6. clear HS5.
(* 0x82c48..0x82c54: s1 = p - 16, a1 = 16, a0 = s1, `jal __asan_unpoison_memory_region`: stops at the fetch of 0x54aa4 *)
fsw_aj_runU fsr_tbl_ok HS6 HJ HARU.
{ fsr_awr_entry_tac B IMG Usp HFP. }
fsr_kb_tac HF W NWB Klo Khi K6.
clear HF HFr HG.
rewrite ?wvb_collapse in HJ, HARU.
lazymatch type of HS6 with st_ok _ _ _ (restrict _ ?m) => rename m into MSU end.
pose proof (fsr_KB_trans _ _ _ _ _ _ (fsr_KB_trans _ _ _ _ _ _ (fsr_KB_trans _ _ _ _ _ _
  (fsr_KB_trans _ _ _ _ _ _ (fsr_KB_trans _ _ _ _ _ _ K1 K2) K3) K4) K5) K6) as KC.
clear K1 K2 K3 K4 K5 K6.
(* ---- at the `jal __asan_unpoison_memory_region` target: registers, statics, frame chunks ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ MSU HS6 eq_refl) as Hshape.
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
assert (R1 : getr (ms_regs MSU) 1 = Z_to_bv 64 FSR_RA_UNPOISON)
  by exact (fsw_reg_lit _ E _ MSU 1%bv 535640 HS6 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (Rsp : spZ (ms_regs MSU) = spZ regs - 32).
{ pose proof (fsw_reg_off _ E _ MSU 2%bv 2 (-32) (spZ regs) HS6 ltac:(vm_compute; reflexivity) Usp
    ltac:(unfold HEAD in *; lia)) as X. unfold spZ at 1. lia. }
assert (R10 : getr (ms_regs MSU) 10 = w64 (p - HEAD)).
{ pose proof (fsw_reg_off _ E _ MSU 10%bv 10 (-16) p HS6 ltac:(vm_compute; reflexivity) U10
    ltac:(unfold HEAD in *; lia)) as X.
  unfold w64. replace (p - HEAD) with (p + -16) by (unfold HEAD; lia). rewrite <- X. symmetry. apply Z_to_bv_bv_unsigned. }
assert (R9 : getr (ms_regs MSU) 9 = w64 (p - HEAD)).
{ pose proof (fsw_reg_off _ E _ MSU 9%bv 10 (-16) p HS6 ltac:(vm_compute; reflexivity) U10
    ltac:(unfold HEAD in *; lia)) as X.
  unfold w64. replace (p - HEAD) with (p + -16) by (unfold HEAD; lia). rewrite <- X. symmetry. apply Z_to_bv_bv_unsigned. }
assert (R11 : getr (ms_regs MSU) 11 = w64 16)
  by exact (fsw_reg_lit _ E _ MSU 11%bv 16 HS6 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R8 : getr (ms_regs MSU) 8 = getr regs 11)
  by exact (fsw_reg_atom (w_H W) regs _ _ MSU 8%bv 11%bv 11 HS6 ltac:(vm_compute; reflexivity) eq_refl).
assert (R18 : bv_unsigned (getr (ms_regs MSU) 18) = SHADOW_OFF)
  by exact (fsw_reg_off _ E _ MSU 18%bv 32 0 SHADOW_OFF HS6 ltac:(vm_compute; reflexivity)
    ltac:(rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
assert (R3 : getr (ms_regs MSU) 3 = getr regs 3)
  by exact (fsw_reg_atom (w_H W) regs _ _ MSU 3%bv 3%bv 3 HS6 ltac:(vm_compute; reflexivity) eq_refl).
assert (R4 : getr (ms_regs MSU) 4 = getr regs 4)
  by exact (fsw_reg_atom (w_H W) regs _ _ MSU 4%bv 4%bv 4 HS6 ltac:(vm_compute; reflexivity) eq_refl).
assert (Rk : forall r, 19 <= r <= 27 -> getr (ms_regs MSU) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. assert (r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc by (clear - Hr; lia).
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
  - exact (fsw_reg_atom (w_H W) regs _ _ MSU (Z_to_bv 5 19) (Z_to_bv 5 19) 19 HS6 ltac:(vm_compute; reflexivity) eq_refl).
  - exact (fsw_reg_atom (w_H W) regs _ _ MSU (Z_to_bv 5 20) (Z_to_bv 5 20) 20 HS6 ltac:(vm_compute; reflexivity) eq_refl).
  - exact (fsw_reg_atom (w_H W) regs _ _ MSU (Z_to_bv 5 21) (Z_to_bv 5 21) 21 HS6 ltac:(vm_compute; reflexivity) eq_refl).
  - exact (fsw_reg_atom (w_H W) regs _ _ MSU (Z_to_bv 5 22) (Z_to_bv 5 22) 22 HS6 ltac:(vm_compute; reflexivity) eq_refl).
  - exact (fsw_reg_atom (w_H W) regs _ _ MSU (Z_to_bv 5 23) (Z_to_bv 5 23) 23 HS6 ltac:(vm_compute; reflexivity) eq_refl).
  - exact (fsw_reg_atom (w_H W) regs _ _ MSU (Z_to_bv 5 24) (Z_to_bv 5 24) 24 HS6 ltac:(vm_compute; reflexivity) eq_refl).
  - exact (fsw_reg_atom (w_H W) regs _ _ MSU (Z_to_bv 5 25) (Z_to_bv 5 25) 25 HS6 ltac:(vm_compute; reflexivity) eq_refl).
  - exact (fsw_reg_atom (w_H W) regs _ _ MSU (Z_to_bv 5 26) (Z_to_bv 5 26) 26 HS6 ltac:(vm_compute; reflexivity) eq_refl).
  - exact (fsw_reg_atom (w_H W) regs _ _ MSU (Z_to_bv 5 27) (Z_to_bv 5 27) 27 HS6 ltac:(vm_compute; reflexivity) eq_refl). }
pose proof HS6 as HS6c. destruct HS6c as (_ & _ & _ & _ & _ & _ & _ & HM6 & _).
assert (Gc : fs_glob tfibsegs W (ms_mem MSU) live peak (cnt + 1) fail).
{ apply (fs_glob_of_TS E W _ _ live peak (cnt + 1) fail (SOff 35 0) (SOff 36 0) (SOff 33 1) (SOff 34 0) HM6).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; first [exact E35 | exact E36 | exact E34]]
    | solve [lazymatch goal with |- sv_denot _ (SOff 33 1) = _ =>
               apply bv_eq; rewrite denot_SOff, E33; rewrite !unsigned_lit_small by lia;
               apply zcanon_id; unfold M64; lia end]
    | solve [lia] ]. }
destruct HM6 as (_ & HR6 & _). cbn [ss_mem] in HR6.
pose proof (Forall_inv HR6) as (_ & _ & _ & HCK).
cbn [YP09.r_chunks YP09.r_base base_val] in HCK. rewrite Usp in HCK.
clear HR6.
(* ---- the unpoison call ---- *)
subst U.
rewrite Hshape. cbn [ss_pc].
eapply SRr_bind.
{ apply (fsw_unpoison16_atU B PC_unpoison UPO STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W _ md [] ly S U1 U2 W
    (ms_mem MSU) _ 0 (ms_regs MSU) (-32) (p - HEAD) (p - HEAD) (k + HEAD) HJ HARU).
  all: first
    [ solve [lazymatch goal with |- spZ _ = _ => rewrite Rsp; lia end]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lazymatch goal with |- ESTACK - _ <= _ => unfold ESTACK; rewrite FR; lia end]
    | solve [lazymatch goal with |- YK0s.ret_ok _ =>
               rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold FSR_RA_UNPOISON; lia); reflexivity end]
    | solve [lazymatch goal with |- getr _ 3 = _ => rewrite R3; exact Hgp end]
    | solve [lazymatch goal with |- getr _ 4 = _ => rewrite R4; exact Htp end]
    | solve [exact R10]
    | solve [exact R11]
    | solve [exact Hblk]
    | solve [rewrite Hrqk; unfold HEAD in *; lia]
    | solve [lia] ]. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP & Hkeep & Hfr).
rewrite R1.
clear Hshape.
(* ---- resume at 0x82c58 (FSW_rres.fsw_resume_after_rtU_args) ---- *)
assert (P2 : getr regs2 2 = getr (ms_regs MSU) 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs MSU) 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs MSU) 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr (ms_regs MSU) 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
set (xs := fsr_xsB regs k cnt fail live peak).
set (E2 := Ereg regs2 (fs_extraT ++ xs)).
assert (E2_2 : bv_unsigned (ew E2 2) = spZ regs - 32)
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2; unfold spZ in Rsp; exact Rsp).
assert (E2_9 : bv_unsigned (ew E2 9) = p - HEAD).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), P9, R9. unfold w64. apply unsigned_lit_small.
  clear - Hb4096 Hp64'; unfold HEAD in *; lia. }
assert (E2_18 : bv_unsigned (ew E2 18) = SHADOW_OFF)
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), P18; exact R18).
assert (V : forall (k0 j : nat) (r : bv 5), nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = getr regs r ->
    Z.of_nat k0 = bv_unsigned r -> sv_denot E (SOff k0 0) = sv_denot E2 (SOff (32 + j) 0)).
{ intros k0 j r Hn Hk. rewrite !fsw_SOff0. subst E2. rewrite ew_Ereg_extra, Hn. subst E. exact (ew_Ereg_nat regs _ k0 r Hk). }
change (ms_mem (restrict (w_H W) MSU)) with (mrestrict (w_H W) (ms_mem MSU)) in HCK.
assert (Hck : Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W) (ms_mem MSU)) (spZ regs - 32)) fsr_cs).
{ unfold fsr_cs.
  constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  - apply (fsr_chunk_move E E2 _ (spZ regs) (spZ regs - 32) (-32) 0 8 (SOff 18 0) (SOff 40 0));
      [ring | exact (V 18%nat 8%nat 18%bv eq_refl eq_refl) | (apply (proj1 (Forall_forall _ _) HCK); cbn; tauto)].
  - apply (fsr_chunk_move E E2 _ (spZ regs) (spZ regs - 32) (-24) 8 8 (SOff 9 0) (SOff 39 0));
      [ring | exact (V 9%nat 7%nat 9%bv eq_refl eq_refl) | (apply (proj1 (Forall_forall _ _) HCK); cbn; tauto)].
  - apply (fsr_chunk_move E E2 _ (spZ regs) (spZ regs - 32) (-16) 16 8 (SOff 8 0) (SOff 38 0));
      [ring | exact (V 8%nat 6%nat 8%bv eq_refl eq_refl) | (apply (proj1 (Forall_forall _ _) HCK); cbn; tauto)].
  - apply (fsr_chunk_move E E2 _ (spZ regs) (spZ regs - 32) (-8) 24 8 (SOff 1 0) (SOff 37 0));
      [ring | exact (V 1%nat 5%nat 1%bv eq_refl eq_refl) | (apply (proj1 (Forall_forall _ _) HCK); cbn; tauto)]. }
(* the statics and the old block's bytes across the call *)
assert (GM2 : fs_glob tfibsegs W mem2 live peak (cnt + 1) fail).
{ apply (fsr_glob_KB W (ms_mem MSU) mem2 _ _ _ _ Gc). intros a Ha.
  pose proof (fsr_pstat_low a Ha) as Hl.
  apply (fsr_KB_unpoison B ly S (U1 ++ (p - HEAD, HEAD) :: U2) (U1 ++ U2) W (ms_mem MSU) mem2 _ md2 a (a + 1) HARU HARU2).
  all: first
    [ solve [intros x Hx; left; unfold SHADOW_OFF; lia]
    | solve [intros x Hx; apply Hfr; [lia | rewrite Rsp; unfold PO_WIN; lia]]
    | solve [lia] ]. }
assert (KU : fsr_KB (w_H W) (ms_mem MSU) mem2 (p - HEAD) (p + k)).
{ apply (fsr_KB_unpoison B ly S (U1 ++ (p - HEAD, HEAD) :: U2) (U1 ++ U2) W (ms_mem MSU) mem2 _ md2 _ _ HARU HARU2 Klo Khi
    HAPPB).
  intros x Hx. apply Hfr; [lia | rewrite Rsp; unfold PO_WIN; pose proof (Hblkr x Hx); lia]. }
pose proof (fsr_KB_trans _ _ _ _ _ _ KC KU) as KH.
assert (Hrs : Forall (region_ok tfibsegs E2 (mrestrict (w_H W) mem2)) fsr_rsB).
{ unfold fsr_rsB. apply Forall_app. split.
  - exact (fsr_pstat_ok W regs2 mem2 live peak (cnt + 1) fail
      ([getr regs 1; getr regs 8; getr regs 9; getr regs 18] ++ [Z_to_bv 64 k]) GM2).
  - constructor; [|constructor].
    apply (fs_head_region_ok B ly S (U1 ++ U2) W mem2 md2 E2 9 (p - HEAD) 0 _ (p - HEAD) (k + HEAD) HARU2 Hblk).
    all: first
      [ solve [exact E2_9]
      | solve [lazymatch goal with |- Forall _ _ =>
                 constructor; [|constructor];
                 apply (fs_head_chunk_ok E2 (w_H W) mem2 (p - HEAD) (SOff 41 0) k);
                 [ rewrite fsw_SOff0; subst E2; exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 9)
                 | exact Hk64
                 | exact (fsr_val_mem_KB (w_H W) mem mem2 (p - HEAD) 8 k (p - HEAD) (p + k) KH
                     ltac:(lia) ltac:(cbn; unfold HEAD in *; lia) Hhead) ] end]
      | solve [rewrite Hrqk; unfold HEAD in *; lia]
      | solve [lia] ]. }
assert (Himg : forall g, (forall x, g <= x < g + 8 -> in_img tfibsegs x) -> p - HEAD + 8 <= g \/ g + 8 <= p - HEAD)
  by (intros g Hg; exact (fs_head_img_apart B ly S W _ md2 (p - HEAD) (k + HEAD) (p - HEAD) g 8 (proj1 HARU2) Hblk
        ltac:(lia) ltac:(rewrite Hrqk; unfold HEAD in *; lia) ltac:(lia) Hg)).
pose proof (Himg 0x9fc10 (fun x Hx => fsr_cells_img x (ex_intro _ (0x9fc10, 0x9fc18) (conj (or_introl eq_refl) Hx)))) as I1.
pose proof (Himg 0xa8438 (fun x Hx => fsr_cells_img x (ex_intro _ (0xa8438, 0xa8440) (conj (or_intror (or_introl eq_refl)) Hx))))
  as I2.
assert (IS : forall g, In (g, g + 8) FS_PSTAT_FP -> p - HEAD + 8 <= g \/ g + 8 <= p - HEAD)
  by (intros g Hg; apply Himg; intros x Hx; exact (fs_pstat_img x (inFP_FS_PSTAT_FP g Hg x Hx))).
pose proof (IS G_FAIL ltac:(vm_compute; tauto)) as I3. pose proof (IS G_LIVE ltac:(vm_compute; tauto)) as I4.
pose proof (IS G_PEAK ltac:(vm_compute; tauto)) as I5. pose proof (IS G_COUNT ltac:(vm_compute; tauto)) as I6.
assert (Hpd : pairwise_disjoint E2 (fsT_ret_regions 32 fsr_cs fsr_rsB)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fsr_rsB, fs_pstat_regions, fs_got_region, fs_bcell_region, fstk_ret, fs_pstat_region,
    fs_head_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2_2, E2_9.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
    G_COUNT, G_FAIL, G_LIVE, G_PEAK in *.
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  pose proof (Hblkr (p - HEAD) ltac:(unfold HEAD; lia)) as Hbs. unfold HEAD in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia | lia]. }
assert (Hgf : atoms_ok E2 fsr_gfB).
{ unfold fsr_gfB. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2_9, E2_18.
  repeat split; first [solve [exact I] | solve [unfold SHADOW_OFF; lia] | solve [change (2 ^ 0) with 1; apply Z.mod_1_r]
    | solve [change (2 ^ 4) with 16; unfold HEAD in *; lia] | solve [unfold HEAD in *; lia]]. }
pose proof (fsw_resume_after_rtU_args B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W _ md [] ly S (U1 ++ U2) W mem2
  md2 0 (ms_regs MSU) regs2 (ms_mem MSU) 32 xs fsr_cs fsr_rsB fsr_gfB FSR_RA_UNPOISON FS_GOT FS_CELL HJ2 HARU2 HP
  Rsp (proj1 F32) (proj2 F32) eq_refl ltac:(vm_compute; reflexivity) Hcsr Hck
  (fun a Ha => Hkeep a ltac:(rewrite Rsp; exact Ha)) Hrs Hpd Hgf) as HS7.
fold E2 in HS7.
clear HS6 HCK Hck Hrs Hpd Hgf V.
(* ---- disown's two checks (token run: both read shadow(s1), s1 = p - 16), the head load, g_live -= k, a1 = n + 16,
   a0 = s1; stops at the fetch of __wrap_realloc 0x530e8 ---- *)
assert (DJ : Forall (zdisjoint (p - HEAD, 16)) (U1 ++ U2))
  by exact (fs_head_apart_rest U1 U2 (p - HEAD) (proj2 (proj1 (proj2 HARU)))).
destruct (fs_head_shadow0 B ly S (U1 ++ U2) W mem2 md2 (p - HEAD) (k + HEAD) HARU2 Hblk
  ltac:(rewrite Hrqk; unfold HEAD in *; lia) DJ) as [Z0 Z1].
assert (UB : U E2 (SOff 18 0) = SHADOW_OFF)
  by (rewrite U_SOff, E2_18, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
assert (U9 : U E2 (SOff 9 0) = p - HEAD)
  by (rewrite U_SOff, E2_9, Z.add_0_r; apply zcanon_id; unfold M64; clear - Hb4096 Hp64'; unfold HEAD in *; lia).
assert (SHOK : sh_ok tfibsegs (SOff 18 0) [YCbn.mkSHE 9 0 16] E2 (mrestrict (w_H W) mem2)).
{ constructor; [|constructor].
  exact (fs_head_shent (SOff 18 0) E2 W mem2 9 (p - HEAD) U9 UB Hh8 Happh Z0 Z1). }
fsw_aj_run_tokU fsr_tbl_ok HS7 HJ2 HARU2 SHOK fs_Bspan.
{ apply (fsr_awr_retH B IMG E2 FSR_RA_UNPOISON 32 STK_fuzz_realloc (spZ regs) fsr_cs fsr_gfB 9
    [YP09.mkChunk 0 (CVal 8 (SOff 41 0))]).
  all: first [solve [exact E2_2] | solve [exact HFP] | solve [rewrite FR; lia]]. }
(* ---- at the `jal __wrap_realloc` target: fsr_at_realloc ---- *)
lazymatch type of HS7 with st_ok _ _ _ (restrict _ ?m) => rename m into MSR end.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?x |} _ => set (MDR := x) in * end.
assert (NWR : forall a, p - HEAD <= a < p + k ->
  ~ in_wrange E2 (ss_mem (fss_retT FSR_RA_UNPOISON 32 fsr_cs fsr_rsB fsr_gfB)) a).
{ intros a Ha. apply (fsr_nw_ret E2 _ a FSR_RA_UNPOISON eq_refl).
  - rewrite E2_2. pose proof (Hblkr a Ha). lia.
  - exact (NIMG a Ha). }
pose proof (fsr_KB_run E2 _ (w_H W) mem2 (ms_mem MSR) (p - HEAD) (p + k) HF Klo Khi NWR) as KT.
pose proof (fsr_KB_trans _ _ _ _ _ _ KH KT) as KZ.
clear HF HFr HG NWR.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ MSR HS7 eq_refl) as Hshape7.
assert (E2_8 : bv_unsigned (ew E2 8) = n).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8, R8, H11. unfold w64. apply unsigned_lit_small.
  clear - Hn64; lia. }
assert (F10 : getr (ms_regs MSR) 10 = w64 (p - HEAD)).
{ pose proof (fsw_reg_off _ E2 _ MSR 10%bv 9 0 (p - HEAD) HS7 ltac:(vm_compute; reflexivity) E2_9 Hh64) as X.
  unfold w64. replace (p - HEAD) with (p - HEAD + 0) by ring. rewrite <- X. symmetry. apply Z_to_bv_bv_unsigned. }
assert (F11 : getr (ms_regs MSR) 11 = w64 (n + HEAD)).
{ pose proof (fsw_reg_off _ E2 _ MSR 11%bv 8 16 n HS7 ltac:(vm_compute; reflexivity) E2_8 Hn16) as X.
  unfold w64, HEAD. rewrite <- X. symmetry. apply Z_to_bv_bv_unsigned. }
assert (F1 : getr (ms_regs MSR) 1 = Z_to_bv 64 A_fuzz_realloc_raB)
  by exact (fsw_reg_lit _ E2 _ MSR 1%bv 535792 HS7 ltac:(vm_compute; reflexivity) ltac:(unfold A_fuzz_realloc_raB; lia)).
assert (Fsp : spZ (ms_regs MSR) = spZ regs - 32).
{ pose proof (fsw_reg_off _ E2 _ MSR 2%bv 2 0 (spZ regs - 32) HS7 ltac:(vm_compute; reflexivity) E2_2 Hsp0) as X.
  unfold spZ at 1. rewrite X. ring. }
assert (F8 : getr (ms_regs MSR) 8 = w64 n).
{ pose proof (fsw_reg_off _ E2 _ MSR 8%bv 8 0 n HS7 ltac:(vm_compute; reflexivity) E2_8 Hn0) as X.
  unfold w64. replace n with (n + 0) by ring. rewrite <- X. symmetry. apply Z_to_bv_bv_unsigned. }
assert (F9 : getr (ms_regs MSR) 9 = w64 (p - HEAD)).
{ pose proof (fsw_reg_off _ E2 _ MSR 9%bv 9 0 (p - HEAD) HS7 ltac:(vm_compute; reflexivity) E2_9 Hh64) as X.
  unfold w64. replace (p - HEAD) with (p - HEAD + 0) by ring. rewrite <- X. symmetry. apply Z_to_bv_bv_unsigned. }
assert (F18 : getr (ms_regs MSR) 18 = w64 k).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 _ MSR 18%bv HS7).
  lazymatch goal with |- sv_denot _ (sr_get ?rr 18%bv) = _ =>
    replace (sr_get rr 18%bv) with (fsr_rd8 (SOff 41 0)) by (vm_compute; reflexivity) end.
  rewrite fsr_rd8_denot, fsw_SOff0. subst E2. exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 9). }
assert (Fkept : fsr_kept B regs (ms_regs MSR)).
{ split; [|split].
  - intros r Hr.
    assert (r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc by (clear - Hr; lia).
    rewrite <- (Rk r Hr), <- (HP r ltac:(unfold acallee_saved; lia)).
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
    + exact (fsw_reg_atom (w_H W) regs2 _ _ MSR (Z_to_bv 5 19) (Z_to_bv 5 19) 19 HS7 ltac:(vm_compute; reflexivity) eq_refl).
    + exact (fsw_reg_atom (w_H W) regs2 _ _ MSR (Z_to_bv 5 20) (Z_to_bv 5 20) 20 HS7 ltac:(vm_compute; reflexivity) eq_refl).
    + exact (fsw_reg_atom (w_H W) regs2 _ _ MSR (Z_to_bv 5 21) (Z_to_bv 5 21) 21 HS7 ltac:(vm_compute; reflexivity) eq_refl).
    + exact (fsw_reg_atom (w_H W) regs2 _ _ MSR (Z_to_bv 5 22) (Z_to_bv 5 22) 22 HS7 ltac:(vm_compute; reflexivity) eq_refl).
    + exact (fsw_reg_atom (w_H W) regs2 _ _ MSR (Z_to_bv 5 23) (Z_to_bv 5 23) 23 HS7 ltac:(vm_compute; reflexivity) eq_refl).
    + exact (fsw_reg_atom (w_H W) regs2 _ _ MSR (Z_to_bv 5 24) (Z_to_bv 5 24) 24 HS7 ltac:(vm_compute; reflexivity) eq_refl).
    + exact (fsw_reg_atom (w_H W) regs2 _ _ MSR (Z_to_bv 5 25) (Z_to_bv 5 25) 25 HS7 ltac:(vm_compute; reflexivity) eq_refl).
    + exact (fsw_reg_atom (w_H W) regs2 _ _ MSR (Z_to_bv 5 26) (Z_to_bv 5 26) 26 HS7 ltac:(vm_compute; reflexivity) eq_refl).
    + exact (fsw_reg_atom (w_H W) regs2 _ _ MSR (Z_to_bv 5 27) (Z_to_bv 5 27) 27 HS7 ltac:(vm_compute; reflexivity) eq_refl).
  - exact (eq_trans (fsw_reg_atom (w_H W) regs2 _ _ MSR 3%bv 3%bv 3 HS7 ltac:(vm_compute; reflexivity) eq_refl)
      (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) (eq_trans R3 Hgp))).
  - exact (eq_trans (fsw_reg_atom (w_H W) regs2 _ _ MSR 4%bv 4%bv 4 HS7 ltac:(vm_compute; reflexivity) eq_refl)
      (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) (eq_trans R4 Htp))). }
pose proof HS7 as HS7c. destruct HS7c as (_ & _ & _ & _ & _ & _ & _ & HM7 & _).
assert (GF : fs_glob tfibsegs W (ms_mem MSR) (live - k) peak (cnt + 1) fail).
{ apply (fs_glob_of_TS E2 W _ _ (live - k) peak (cnt + 1) fail (SAlu ALU_SUB (SOff 35 0) (fsr_rd8 (SOff 41 0)))
    (SOff 36 0) (SOff 33 0) (SOff 34 0) HM7).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [lazymatch goal with |- sv_denot _ (SOff 36 0) = _ =>
               rewrite fsw_SOff0; subst E2; exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 4) end]
    | solve [lazymatch goal with |- sv_denot _ (SOff 33 0) = _ =>
               rewrite fsw_SOff0; subst E2; exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 1) end]
    | solve [lazymatch goal with |- sv_denot _ (SOff 34 0) = _ =>
               rewrite fsw_SOff0; subst E2; exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 2) end]
    | solve [lazymatch goal with |- sv_denot _ (SAlu ALU_SUB _ _) = _ =>
               apply bv_eq; change (bv_unsigned (sv_denot E2 (SAlu ALU_SUB (SOff 35 0) (fsr_rd8 (SOff 41 0)))))
                 with (U E2 (SAlu ALU_SUB (SOff 35 0) (fsr_rd8 (SOff 41 0))));
               rewrite U_SAlu; cbn [zalu_raw];
               assert (H35 : U E2 (SOff 35 0) = live)
                 by (apply U_atom; [subst E2; exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 3) | exact Hlv64]);
               assert (H41 : U E2 (fsr_rd8 (SOff 41 0)) = k)
                 by (unfold U; rewrite fsr_rd8_denot; fold (U E2 (SOff 41 0)); apply U_atom;
                     [subst E2; exact (ew_Ereg_extra regs2 (fs_extraT ++ xs) 9) | exact Hk64]);
               rewrite H35, H41, unsigned_lit_small by exact Hlk64; apply zcanon_id; unfold M64; exact Hlk64 end]
    | solve [exact Hlk] | solve [exact Hp64] | solve [exact Hc1] | solve [exact Hf64] ]. }
destruct HM7 as (_ & HR7 & _). cbn [ss_mem] in HR7.
pose proof (Forall_inv HR7) as (_ & _ & _ & HCK7).
cbn [YP09.r_chunks YP09.r_base base_val] in HCK7. rewrite E2_2 in HCK7.
change (ms_mem (restrict (w_H W) MSR)) with (mrestrict (w_H W) (ms_mem MSR)) in HCK7.
clear HR7.
assert (FV : forall (off : Z) (j : nat) (r : bv 5), In (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0))) fsr_cs ->
    nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = getr regs r ->
    val_mem tfibsegs (mrestrict (w_H W) (ms_mem MSR)) (spZ regs - 32 + off) 8 (bv_unsigned (getr regs r))).
{ intros off j r Hin Hn.
  apply (fsr_val_of_chunk8 E2 _ (spZ regs - 32) off (SOff (32 + j) 0)); [| | apply u64_range | reflexivity].
  - exact (proj1 (Forall_forall _ _) HCK7 _ Hin).
  - rewrite fsw_SOff0, Z_to_bv_bv_unsigned. subst E2. rewrite ew_Ereg_extra. exact Hn. }
rewrite Hshape7. cbn [ss_pc].
apply SRr_ret.
exists (ms_regs MSR), (ms_mem MSR), MDR.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HARU2|].
split; [exact F10|]. split; [exact F11|]. split; [exact F1|]. split; [exact Fsp|]. split; [exact F8|].
split; [exact F9|]. split; [exact F18|]. split; [exact Fkept|].
split.
{ unfold fsr_frame_vals.
  replace (spZ regs - 32) with (spZ regs - 32 + 0) by ring.
  replace (spZ regs - 24) with (spZ regs - 32 + 8) by ring.
  replace (spZ regs - 16) with (spZ regs - 32 + 16) by ring.
  replace (spZ regs - 8) with (spZ regs - 32 + 24) by ring.
  split; [exact (FV 0 8%nat 18%bv ltac:(cbn; tauto) eq_refl)|].
  split; [exact (FV 8 7%nat 9%bv ltac:(cbn; tauto) eq_refl)|].
  split; [exact (FV 16 6%nat 8%bv ltac:(cbn; tauto) eq_refl)|].
  exact (FV 24 5%nat 1%bv ltac:(cbn; tauto) eq_refl). }
split; [exact GF|].
unfold zbytes_at in *.
exact (fsr_garr8_KB (w_H W) mem (ms_mem MSR) p old (p - HEAD) (p + k) KZ ltac:(unfold HEAD; lia)
  ltac:(rewrite Hlen; lia) HZB).
Qed.
End s.
