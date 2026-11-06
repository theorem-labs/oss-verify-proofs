(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 1266 of its 1332 lines of code are new or changed and 1014 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_dec_E.v, with its module paths, module names and numbers changed; 1247 of its 1346 lines of code are new or changed and 1233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put.v; 214 of its 336 lines of code are new or changed and 1224 lines of the source are left out. *)
(* fs WRITER walk, image B (fs.asan-ubsan): the ENTRY segment of put's GROW arm (preset_file.c:454-476, A_put 0x8449c),
   the case `failed = 0 /\ cap < len + n + 1`, the image-B twin of lib/A/FSW_put_grow_entry.v. From the entry pc to
   the doubling-loop head 0x84564 (542052): the prologue, UBSan's alignment check of o (0x844d8 / 0x844dc), the inline
   ASan checks of o + 24, o + 8 and o + 16, the need test 0x8454c (its BC_LTU side), the spill of o + 8 at 0x84550, the
   `cap <> 0` test 0x84554 and both of its sides; each side reaches the loop head with the first candidate capacity in
   s6 (reg 22), which is re-seated on the FRESH atom 36, so both sides meet in ONE head state,
   lib/B/FSW_put_grow.v fsw_pg_ssl. The rest of the arm is an ABSTRACT continuation.

   MEASURED on B (token engine, lane scratch probe, a build machine workspace (internal path), 2026-10-29T09:2xZ;
   Bx := FSW_K.fs_Bx, Bspan := FSW_K.fs_Bspan, SH := FSW_put.fsw_pf_SH; every run sh_j = 0, sh_chk = true,
   sh_obls = []):
   - run 1 from fsw_pge_ss0 (run_K 36) stops at 542028 = 0x8454c, SR_branch BC_GEU cap (n + 1 + len); the alignment
     check 0x844dc and the shadow checks 0x84504 / 0x84520 / 0x84534 do not stop it (atom 10's af_al2 = 3 and the
     shadow entry of o's 32 bytes);
   - its BC_LTU side runs to 542036 = 0x84554, SR_branch BC_NE cap 0;
   - cap <> 0 side: runs to 542052 with reg 22 = SLL cap 1, reg 11 = SLL cap 2; cap = 0 side: runs to 542052 with
     reg 22 = SLit 4096, reg 11 = SLit 8192; every other register is fsw_pg_regs', and ss_mem is fsw_pg_mem on both
     sides. So the route, the two candidates and the re-seat are A's; only the pcs, the code table and the
     registers (B's s3 / s4 swap and need in a0) differ, and they live in the state definitions.

   TAKEN FROM: lib/A/FSW_put_grow_entry.v at a working branch 860b2fb1188 (the same blob is on
   a working branch f0e2574c33c): fsw_pge_ss0, fsw_pge_class_le, fsw_pge_U_sll, fsw_pge_seat and
   fsw_pg_entry_run unchanged in form (B's table fsw_put_tbl_ok for A's fsw_wr_tbl_ok).

   RULE-24: proves function put (omx-clap-core/fuzz_state, image B = asan-ubsan, entry 0x8449c; the GROW arm)
   (reuse search: proof-index put_holds / put_close_grow / fsw_pg_loop / pgt_run / fsw_pg_entry_run, index v5
   built 2026-10-29T07:26:27Z, plus a git grep with a passing control (put_failed_run) of 599 cold lib/B trees: no
   lib/B/FSW_put_grow* or FSW_put_holds* anywhere; checker a Theorem Labs lane CONFIRM 09:2xZ). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSW_K FSW_ret FSW_put FSW_put_grow.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the entry state: fsw_pf_ss0's regions, with the head's atom facts fsw_pg_gf (atom 33 admits the NULL buffer
   of cap = 0) ---- *)
Definition fsw_pge_ss0 : sstate := fss0T_args A_put FRAME_put [fsw_pf_o_region] fsw_pg_gf.

(* a buffer class 4096 * 2 ^ j below WMAX doubles to at most WMAX *)
Lemma fsw_pge_class_le : forall cap j, 0 <= j -> cap = 4096 * 2 ^ j -> cap < 2 ^ 27 ->
  4096 <= cap /\ 2 * cap <= 2 ^ 27.
Proof.
intros cap j Hj Hc Hlt. subst cap.
pose proof (Z.pow_le_mono_r 2 0 j ltac:(lia) Hj) as H0. change (2 ^ 0) with 1 in H0.
destruct (Z.le_gt_cases j 14) as [Hle|Hgt].
- pose proof (Z.pow_le_mono_r 2 j 14 ltac:(lia) Hle) as H1. change (2 ^ 14) with 16384 in H1. lia.
- pose proof (Z.pow_le_mono_r 2 15 j ltac:(lia) ltac:(lia)) as H1. change (2 ^ 15) with 32768 in H1. lia.
Qed.
(* the value of a left shift by a literal that does not overflow *)
Lemma fsw_pge_U_sll : forall E a (k x : Z), YP0e.U E a = x -> 0 <= k < 64 -> 0 <= x * 2 ^ k < 2 ^ 64 ->
  YP0e.U E (SAlu ALU_SLL a (SLit k)) = x * 2 ^ k.
Proof.
intros E a k x Ha Hk Hx. rewrite U_SAlu, U_SLit, Ha. cbn [zalu_raw].
rewrite (zcanon_id k) by (unfold M64; lia).
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite (Z.mod_small k) by (change (2 ^ 6) with 64; lia).
rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the loop head's re-seat: s6 (reg 22) holding the candidate c becomes the fresh atom 36, a1 (reg 11) holding 2 * c
   is re-pinned to `c << 1`, and the facts are replaced by the head's (FSW_K.v:839-857 fsw_reseat_atom's steps) *)
Lemma fsw_pge_seat : forall E ss ms c G,
  st_ok tfibsegs E ss ms -> ss_atoms_lt 36 ss = true ->
  getr (ms_regs ms) 22%bv = Z_to_bv 64 c -> getr (ms_regs ms) 11%bv = Z_to_bv 64 (2 * c) ->
  0 <= c -> 2 * c < 2 ^ 64 ->
  facts_ok (ewset E 36 (Z_to_bv 64 c)) G ->
  st_ok tfibsegs (ewset E 36 (Z_to_bv 64 c))
    (mkSS (ss_pc ss) (sr_set (sr_set (ss_regs ss) 22%bv (SOff 36 0)) 11%bv (SAlu ALU_SLL (SOff 36 0) (SLit 1)))
       (ss_mem ss) (ss_resv ss) G) ms.
Proof.
intros E ss ms c G HS Hat V22 V11 Hc0 Hc1 FOK.
pose proof (YP03.st_ok_abstract_reg tfibsegs 36 E ss ms 22%bv HS Hat ltac:(vm_compute; reflexivity)) as HS1.
rewrite V22 in HS1.
assert (V11' : getr (ms_regs ms) 11%bv = sv_denot (ewset E 36 (Z_to_bv 64 c)) (SAlu ALU_SLL (SOff 36 0) (SLit 1))).
{ rewrite V11, denot_lit_U. f_equal. symmetry.
  rewrite (fsw_pge_U_sll _ (SOff 36 0) 1 c); [change (2 ^ 1) with 2; lia | | lia | change (2 ^ 1) with 2; lia].
  apply U_atom; [apply ew_ewset_same | lia]. }
pose proof (YI08.st_ok_set_reg tfibsegs (ewset E 36 (Z_to_bv 64 c)) _ ms 11%bv _ HS1
  ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq) V11') as HS2.
exact (YP06.st_ok_facts tfibsegs _ _ ms G HS2 FOK).
Qed.

Variable B : asyms.
(* the dynamic shadow base's two cells, as FSW_K's entry asks them (lib/B/FSH_Base.v FsShadowSyms; as lib/B/FSW_put.v) *)
Hypothesis HSS : FsShadowSyms B.

(* put's entry to the doubling-loop head on the GROW arm. Premises: put_spec's own (lib/B/FSH_Fn_writer.v put_spec),
   narrowed to failed = 0 and the grow test; 0 <= n is put_spec's Z.of_nat (length bs) = n. The continuation gets
   the head state over an env that agrees with the entry env below atom 36, atom 36 = the first candidate c. *)
Lemma fsw_pg_entry_run :
  forall ly S U W regs mem md ch ot o n buf cap (text : list Z) Q,
  fpreU tfibsegs B STK_put ly S U W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 12 = w64 n ->
  wout_ok B tfibsegs ly S W mem o buf cap 0 text ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  0 <= n ->
  Z.of_nat (length text) + n + 1 <= WMAX ->
  cap < Z.of_nat (length text) + n + 1 ->
  (forall (E : env) (ms : machine_state) (mdc : Model) (c : Z),
     st_ok tfibsegs E fsw_pg_ssl (restrict (w_H W) ms) ->
     sh_ok tfibsegs fs_Bx fsw_pf_SH E (mrestrict (w_H W) (ms_mem ms)) ->
     ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
       ly S W (unpoison U mem) md [] ly S W (unpoison U (ms_mem ms)) mdc 0 ->
     ARU tfibsegs B ly S U W (ms_mem ms) mdc ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FRAME_put <= a < spZ regs) ->
        ms_mem ms (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) ->
     YP06.env_agree 36
       (Ereg regs (fs_extraT ++ [Z_to_bv 64 buf; Z_to_bv 64 (Z.of_nat (length text)); Z_to_bv 64 cap])) E ->
     ew E 36 = Z_to_bv 64 c ->
     c = (if cap =? 0 then 4096 else 2 * cap) ->
     SRr tfibsegs W (mkCfg ms mdc) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md) Q.
Proof.
intros ly S U W regs mem md ch ot o n buf cap text Q
  HPRE G10 G12 HOUT Hspo Hoot Hot16 Hottop HPRESENT Hn0 HWM HGROW K.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold w64 in G10, G12.
unfold WMAX in HWM.
(* ---- the entry facts (as put_fast_run) ---- *)
destruct HPRE as (HPREU & HRO).
pose proof (fsw_ARU B STK_put ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch HPREU) as (Hal16 & Hspc & Hsp47 & _).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
set (len := Z.of_nat (length text)) in *.
assert (Hlen0 : 0 <= len) by (unfold len; lia).
assert (Ho47 : o + 32 <= 2 ^ 47) by lia.
(* the buffer: NULL at cap = 0, else a live block's 16-aligned user bytes below alloc_ceiling, cap a class *)
assert (HBUF : 0 <= buf <= fsw_pf_CEIL /\ buf mod 16 = 0 /\ (cap = 0 \/ 4096 <= cap /\ 2 * cap <= 2 ^ 27)).
{ destruct Hcase as [(Hc0 & Hb0 & _) | ((j & Hj & Hcj) & HRB & _ & _)].
  - subst buf. unfold fsw_pf_CEIL. split; [lia|]. split; [reflexivity | left; exact Hc0].
  - pose proof HRB as (Hin & Hb16 & Hcap0 & _).
    destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin)
      as (_ & Hb4096 & Hbceil & _).
    assert (RQB : req_size (cap + HEAD) = cap + HEAD)
      by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
    rewrite RQB in Hbceil. unfold HEAD in Hbceil, Hb4096. unfold fsw_pf_CEIL.
    split; [lia|]. split; [exact Hb16|]. right.
    apply (fsw_pge_class_le cap j); lia. }
destruct HBUF as (Hbuf & Hb16 & HCLS). clear Hcase.
unfold fsw_pf_CEIL in Hbuf.

(* ---- the entry environment: atoms 33 / 34 / 35 are o's buf / len / cap (FSW_K xatom 0..2) ---- *)
set (xs := [Z_to_bv 64 buf; Z_to_bv 64 len; Z_to_bv 64 cap]).
set (E := Ereg regs (fs_extraT ++ xs)).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (unfold E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact G12).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by (unfold E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 len) by (unfold E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 cap) by (unfold E; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E10u : bv_unsigned (ew E 10) = o) by (rewrite E10; apply wz; lia).
assert (E12u : bv_unsigned (ew E 12) = n) by (rewrite E12; apply wz; lia).
assert (E32u : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
assert (E33u : bv_unsigned (ew E 33) = buf) by (rewrite E33; apply wz; lia).
assert (E34u : bv_unsigned (ew E 34) = len) by (rewrite E34; apply wz; lia).
assert (E35u : bv_unsigned (ew E 35) = cap) by (rewrite E35; apply wz; lia).
(* ---- the entry symbolic state ---- *)
assert (HS : st_ok tfibsegs E fsw_pge_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_put) mem (seg_rom tfibsegs)))).
{ unfold fsw_pge_ss0.
  apply (fsw_entryT_argsX B STK_put FRAME_put ly S U W regs mem md ch A_put [fsw_pf_o_region] fsw_pg_gf xs
    (proj1 HSS) (proj2 HSS) HPREU).
  - split; vm_compute; discriminate.
  - vm_compute; reflexivity.
  - fold E. constructor; [|constructor].
    unfold fsw_pf_o_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10u. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (chunk_ok_val tfibsegs E _ o 0 8 (SOff 33 0) buf);
        [rewrite fsw_SOff0; exact E33 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | rewrite Z.add_0_r; exact Vbuf].
    + apply (chunk_ok_val tfibsegs E _ o 8 8 (SOff 34 0) len);
        [rewrite fsw_SOff0; exact E34 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Vlen].
    + apply (chunk_ok_val tfibsegs E _ o 16 8 (SOff 35 0) cap);
        [rewrite fsw_SOff0; exact E35 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Vcap].
    + apply (chunk_ok_val tfibsegs E _ o 24 4 (SLit 0) 0);
        [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Vfail].
  - fold E. apply pairwise_disjoint_of_extents.
    unfold fsT_regions_args, fsT_regions, fstk, fs_got_region, fs_bcell_region, fsw_pf_o_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E10u.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FRAME_put.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - fold E. unfold fsw_pg_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E10u, E33u, E34u, E35u, E12u. unfold fsw_pf_CEIL.
    change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
(* ---- the journal, window top raised to ot (FSH_Fn_FORM.md 3a); the segment costs no tick ---- *)
assert (HJ0 : ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
                ly S W (unpoison U mem) md [] ly S W (unpoison U mem) md 0).
{ apply (fsw_ajournal_init_ot B STK_put (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S U W regs mem md ch ot HPREU);
    [lia | exact Hot16 | exact Hottop | exact HPRESENT]. }
(* ---- the shadow entry of o's 32 bytes, on the MACHINE's memory (as put_fast_run) ---- *)
assert (HLO : layout_ok ly) by exact (am_layout _ _ _ _ (proj1 HAR)).
pose proof (lo_top ly HLO) as LTOP.
assert (Hlo8 : ly_stk_lo ly mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & L5 & _). unfold page_aligned in L5.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L5]]. }
assert (Hhi8 : ly_stk_hi ly mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & _ & L6 & _). unfold page_aligned in L6.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L6]]. }
assert (HRA32 : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF o 32).
{ assert (HZS0 : zero_shadow (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF
                  (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)).
  { exact (al_zshadow _ _ LAWS ly S W (unpoison U mem) md
             (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR (or_introl eq_refl)). }
  (* the stack's shadow does not depend on U (FSupoisonStack, a Theorem Labs lane) *)
  apply (proj1 (fsw_ARU_stack_ra tfibsegs B LAWS ly S U W mem md (w_H W) o 32 HARU0 ltac:(lia) ltac:(lia))).
  eapply range_addressable_sub;
    [ apply (zero_shadow_range (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF
               (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) Hlo8
               ltac:(rewrite Zminus_mod, Hlo8, Hhi8; reflexivity) HZS0)
    | lia | lia]. }
assert (SHOK : sh_ok tfibsegs fs_Bx fsw_pf_SH E (mrestrict (w_H W) mem)).
{ unfold fsw_pf_SH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 10%nat o 32 o 0 32 HRA32).
  - unfold fs_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 10 o E10). lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. lia. }
(* ---- the two tests' operands, and the head's facts for any candidate in [4096, WMAX] ---- *)
assert (UA : YP0e.U E (SOff 35 0) = cap) by (apply (U_atom E 35 cap E35); lia).
assert (UB : YP0e.U E (SAlu ALU_ADD (SOff 12 1) (SOff 34 0)) = n + 1 + len).
{ rewrite U_SAlu, (U_atom E 34 len E34) by lia. rewrite U_SOff, E12u. cbn [zalu_raw].
  rewrite (zcanon_id (n + 1)) by (unfold M64; lia). apply zcanon_id. unfold M64; lia. }
assert (FOK : forall c, 4096 <= c <= 2 ^ 27 -> facts_ok (ewset E 36 (Z_to_bv 64 c)) fsw_pg_facts).
{ intros c Hc.
  assert (A : forall i, i <> 36%nat -> ew (ewset E 36 (Z_to_bv 64 c)) i = ew E i)
    by (intros i Hi; apply ew_ewset_other; exact Hi).
  unfold facts_ok, fsw_pg_facts, fsw_pg_gf. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite ew_ewset_same, (wz c) by lia.
  rewrite !A by discriminate.
  rewrite E2, E32u, E10u, E33u, E34u, E35u, E12u. unfold fsw_pf_CEIL.
  change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia. }

assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
(* ---- run 1: the prologue, UBSan's alignment check of o and the inline check of o + 24, o + 8, o + 16, to the
   need test 0x8454c ---- *)
unfold cfg_at.
fsw_aj_run_tokU fsw_put_tbl_ok HS HJ0 HARU0 SHOK fs_Bspan.
- cbv [fsw_pge_ss0 fss0T_args fsT_regions_args fsT_regions ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
    [reflexivity | rewrite E2; lia | cbv [fstk YP09.r_wlo]; unfold FRAME_put; lia
    | cbv [fstk YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fsw_pf_o_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
- (* the run wrote only put's frame *)
  assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
    ms_mem ms (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
    vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?E2 in Hr; lia. }
  pose proof (fun a => apresent_grows _ _ _ a HG) as PR1.
  clear HF HFr HG.
  (* the need test: the BC_GEU side is the fast arm, excluded by the grow premise *)
  srr_branch_tok fsw_put_tbl_ok HS SHOK fs_Bspan.
  1: { exfalso. rewrite branch_geu_U, UA, UB in Hc. apply negb_true_iff in Hc. apply Z.ltb_ge in Hc. lia. }
  clear Hc.
  (* ---- run 2: the spill of o + 8 at 0x84550, to the `cap <> 0` test 0x84554 ---- *)
  fsw_aj_run_tokU fsw_put_tbl_ok HS HJ0 HARU0 SHOK fs_Bspan.
  + lazymatch goal with |- context C [ss_mem ?ssx] =>
      let rs' := eval vm_compute in (ss_mem ssx) in
      let g := context C [rs'] in change g end.
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
      [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_nil.
  + assert (MT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
      ms_mem ms0 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hna. rewrite <- (M1 a Ha Hna). apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
      vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?E2 in Hr; lia. }
    pose proof (fun a Ha => apresent_grows _ _ _ a HG (PR1 a Ha)) as PRT.
    clear M1 PR1 HF HFr HG.
    srr_branch_tok fsw_put_tbl_ok HS SHOK fs_Bspan.
    * (* ---- cap <> 0: the first candidate is 2 * cap ---- *)
      rewrite branch_ne_U, UA, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc.
      destruct HCLS as [HC0 | (Hc4096 & Hc27)]; [exfalso; exact (Hc HC0)|].
      fsw_aj_run_tokU fsw_put_tbl_ok HS HJ0 HARU0 SHOK fs_Bspan.
      -- lazymatch goal with |- context C [ss_mem ?ssx] =>
           let rs' := eval vm_compute in (ss_mem ssx) in
           let g := context C [rs'] in change g end.
         eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
           [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |].
         apply awr_ok_cons_ro; [cbn; lia|].
         apply awr_ok_cons_ro; [cbn; lia|].
         apply awr_ok_cons_ro; [cbn; lia|].
         apply awr_ok_nil.
      -- assert (M3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
           ms_mem ms1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
         { intros a Ha Hna. rewrite <- (MT a Ha Hna). apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
           vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
             cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?E2 in Hr; lia. }
         pose proof (fun a Ha => apresent_grows _ _ _ a HG (PRT a Ha)) as PR3.
         clear MT PRT HF HFr HG.
         assert (V22 : getr (ms_regs ms1) 22%bv = Z_to_bv 64 (2 * cap)).
         { pf_reg HS. rewrite denot_lit_U. f_equal.
           rewrite (fsw_pge_U_sll E (SOff 35 0) 1 cap);
             [change (2 ^ 1) with 2; lia | exact UA | lia | change (2 ^ 1) with 2; lia]. }
         assert (V11 : getr (ms_regs ms1) 11%bv = Z_to_bv 64 (2 * (2 * cap))).
         { pf_reg HS. rewrite denot_lit_U. f_equal.
           rewrite (fsw_pge_U_sll E (SOff 35 0) 2 cap);
             [change (2 ^ 2) with 4; lia | exact UA | lia | change (2 ^ 2) with 4; lia]. }
         pose proof (fsw_pge_seat E _ _ (2 * cap) fsw_pg_facts HS) as HS'.
         specialize (HS' ltac:(vm_compute; reflexivity) V22 V11 ltac:(lia) ltac:(lia) (FOK (2 * cap) ltac:(lia))).
         lazymatch type of HS' with st_ok _ _ ?ssx _ =>
           replace ssx with fsw_pg_ssl in HS' by (vm_compute; reflexivity) end.
         apply (K (ewset E 36 (Z_to_bv 64 (2 * cap))) ms1 _ (2 * cap) HS').
         ++ apply sh_ok_agree with (k := 36%nat) (E := E);
              [apply env_agree_ewset | vm_compute; reflexivity | exact SHOK].
         ++ exact HJ0.
         ++ exact HARU0.
         ++ exact M3.
         ++ exact PR3.
         ++ exact (env_agree_ewset E 36 _).
         ++ apply ew_ewset_same.
         ++ rewrite (proj2 (Z.eqb_neq cap 0) Hc). reflexivity.
    * (* ---- cap = 0: the first candidate is 4096 ---- *)
      rewrite branch_ne_U, UA, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc.
      fsw_aj_run_tokU fsw_put_tbl_ok HS HJ0 HARU0 SHOK fs_Bspan.
      -- lazymatch goal with |- context C [ss_mem ?ssx] =>
           let rs' := eval vm_compute in (ss_mem ssx) in
           let g := context C [rs'] in change g end.
         eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
           [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |].
         apply awr_ok_cons_ro; [cbn; lia|].
         apply awr_ok_cons_ro; [cbn; lia|].
         apply awr_ok_cons_ro; [cbn; lia|].
         apply awr_ok_nil.
      -- assert (M3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
           ms_mem ms1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
         { intros a Ha Hna. rewrite <- (MT a Ha Hna). apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
           vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
             cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?E2 in Hr; lia. }
         pose proof (fun a Ha => apresent_grows _ _ _ a HG (PRT a Ha)) as PR3.
         clear MT PRT HF HFr HG.
         assert (V22 : getr (ms_regs ms1) 22%bv = Z_to_bv 64 4096).
         { pf_reg HS. rewrite denot_lit_U, U_SLit. reflexivity. }
         assert (V11 : getr (ms_regs ms1) 11%bv = Z_to_bv 64 (2 * 4096)).
         { pf_reg HS. rewrite denot_lit_U, U_SLit. reflexivity. }
         pose proof (fsw_pge_seat E _ _ 4096 fsw_pg_facts HS) as HS'.
         specialize (HS' ltac:(vm_compute; reflexivity) V22 V11 ltac:(lia) ltac:(lia) (FOK 4096 ltac:(lia))).
         lazymatch type of HS' with st_ok _ _ ?ssx _ =>
           replace ssx with fsw_pg_ssl in HS' by (vm_compute; reflexivity) end.
         apply (K (ewset E 36 (Z_to_bv 64 4096)) ms1 _ 4096 HS').
         ++ apply sh_ok_agree with (k := 36%nat) (E := E);
              [apply env_agree_ewset | vm_compute; reflexivity | exact SHOK].
         ++ exact HJ0.
         ++ exact HARU0.
         ++ exact M3.
         ++ exact PR3.
         ++ exact (env_agree_ewset E 36 _).
         ++ apply ew_ewset_same.
         ++ rewrite Hc. reflexivity.
Qed.
End w.
