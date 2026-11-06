(* preset_base64_decode (fs.asan 0x8481c), part L1 of the Theorem Labs lane walk (a Theorem Labs lane): the symbolic state at the
   loop head 0x848bc (decL_head_st) and the unpacking tactic of dec_head. SCRATCH part (owner a Theorem Labs lane). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_dec_defs FSW_dec_L0 FSW_dec_L2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- unpacking the head ---- *)
Ltac decL_unhead HH :=
  unfold dec_head in HH; cbv zeta in HH;
  destruct HH as (HJ & HARU & Hk & HUc & Hheads & Hbl & Hq & Hrb & Hra & Hcf & Hglob & Hsp & R3 & R4 & R8 & R9 &
    R18 & R19 & R20 & R21 & R22 & R23 & Hacc & R24 & R25 & R26 & R27 & HFr & HLs & HKe & HZb & Hi & Hpad & Hsix &
    Hsix64 & Hlast & Hscan).

Section L1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.

(* ==== TEMPORARY copies of the helper lemmas (FSW_dec_L3.v a Theorem Labs lane), swapped for the imports when they land ==== *)
Hypothesis XLB_text : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  4096 <= d_text d /\ d_text d + Z.of_nat (length (d_tb d)) + 1 <= alloc_ceiling /\
  (forall a, d_text d <= a <= d_text d + Z.of_nat (length (d_tb d)) ->
     ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416) /\
     ~ (q - HEAD <= a < q - HEAD + req_size (d_n d + HEAD)) /\
     (a + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= a) /\
     (a + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= a)).

Hypothesis XLB_q : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  q mod 16 = 0 /\ 4096 + HEAD <= q /\ q + d_n d <= alloc_ceiling /\ 1 <= d_n d /\
  (q + d_n d <= SHADOW_OFF \/ kHighMemBeg <= q) /\
  ~ In (q - HEAD, d_n d + HEAD) (ablocks B (d_ly d) (d_S d)) /\
  (forall a, q <= a < q + d_n d ->
     ~ YG0d.in_img tfibsegs a /\ in_tmp_block (ablocks B (d_ly d) (d_S d)) (ablocks B lyc Sc) a /\
     (a + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= a) /\
     (a + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= a)).

Lemma decL_w64u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply wz. exact Hz. Qed.

(* the n-th byte of the text and its NUL *)
Lemma decL_text_byte : forall d (W : world tfibsegs) mem (i : nat),
  cstr_ok tfibsegs W mem (d_text d) (d_tb d) -> (i <= length (d_tb d))%nat ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (d_text d + Z.of_nat i) 1 (nth i (d_tb d ++ [0]) 0) /\
  0 <= nth i (d_tb d ++ [0]) 0 < 256.
Proof.
intros d W mem i ((HG & _) & _) Hi. apply HG. rewrite length_app. cbn [length]. lia.
Qed.

(* ---- the symbolic state at the head, its shadow entry for the text byte ---- *)
Lemma decL_head_st : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  let c := nth i (d_tb d ++ [0]) 0 in
  st_ok tfibsegs (decL_E d regsc [Z_to_bv 64 c]) decL_hss
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs))) /\
  sh_ok tfibsegs decL_Bx decL_hSH (decL_E d regsc [Z_to_bv 64 c]) (mrestrict (w_H Wc) memc).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH c.
pose proof asan_consts as (C1 & _ & _ & _).
pose proof (XLB_text d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (T1 & T2 & T3).
pose proof (decL_lenp_range B d HE) as (L1 & L2 & _).
pose proof HH as HH0. decL_unhead HH.
pose proof HKe as (_ & _ & HCS & _).
pose proof HCS as ((_ & _) & _ & _ & Hlen32 & _ & HRA & _).
destruct (decL_text_byte d Wc memc i HCS Hi) as (Vc & Rc). fold c in Vc, Rc.
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 (proj1 HE))) as (Hsp16 & Hsp1 & Hsp2 & _).
assert (HSTK : 112 <= STK_preset_base64_decode) by (vm_compute; discriminate).
set (E := decL_E d regsc [Z_to_bv 64 c]).
assert (E18 : bv_unsigned (ew E 18) = d_text d + Z.of_nat i).
{ unfold E. rewrite (decL_E_reg d regsc _ 18 18%bv eq_refl), R18. apply decL_w64u. lia. }
assert (E47 : ew E 47 = Z_to_bv 64 c) by (unfold E; exact (decL_E_ex d regsc _ 0)).
split.
- apply (decL_build B HSS d Wc lyc Sc Uc regsc memc mdc k [Z_to_bv 64 c] DEC_HEAD [decL_txr] decL_hgf HE HJ HARU
    Hsp HFr HLs).
  + vm_compute. reflexivity.
  + fold E. constructor; [|constructor].
    unfold decL_txr, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs E _ _ 0 1 (SOff 47 0) c);
      [rewrite fsw_SOff0, E47; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | rewrite Z.add_0_r; exact Vc].
  + fold E. apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, decL_txr, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
    assert (E2 : bv_unsigned (ew E 2) = d_sp d - DEC_F)
      by (unfold E; rewrite (decL_E_reg d regsc _ 2 2%bv eq_refl); exact Hsp).
    rewrite E2, E18.
    destruct (T3 (d_text d + Z.of_nat i) ltac:(lia)) as (_ & _ & G1 & G2).
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, DEC_F, d_sp in *.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct G1 as [G1|G1]; destruct G2 as [G2|G2];
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  + fold E. unfold decL_hgf, decL_sgf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    pose proof (XLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH0) as (Q16 & Q1 & Q2 & _).
    pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Htb & _).
    pose proof (WriterSpecFacts.six_bytes_length six) as Hnb.
    assert (Hbits : 0 <= 6 * Z.of_nat (length six) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hbits2 : (6 * Z.of_nat (length six) mod 8) mod 2 = 0) by (Z.div_mod_to_equations; lia).
    assert (Hnb2 : 6 * Z.of_nat (length six) / 8 <= 2 ^ 30) by (Z.div_mod_to_equations; lia).
    unfold E; rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 8 8%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 9 9%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 18 18%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 19 19%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 20 20%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 21 21%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 22 22%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 23 23%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 24 24%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 25 25%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 26 26%bv eq_refl). rewrite (decL_E_reg d regsc [Z_to_bv 64 c] 27 27%bv eq_refl).
    fold E. rewrite E47.
    rewrite R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
    pose proof Hrb as (_ & _ & Hn0 & _). assert (HEADv : HEAD = 16) by reflexivity.
    rewrite (decL_w64u DEC_WSMASK) by (unfold DEC_WSMASK; lia).
    rewrite (decL_w64u q) by lia.
    rewrite (decL_w64u (d_text d + Z.of_nat i)) by lia.
    rewrite (decL_w64u G_B64) by (unfold G_B64; lia).
    rewrite (decL_w64u SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (decL_w64u (Z.of_nat (length (WriterSpec.six_bytes six)))) by lia.
    rewrite (decL_w64u acc) by lia.
    rewrite (decL_w64u (6 * Z.of_nat (length six) mod 8)) by lia.
    rewrite (decL_w64u 61) by lia.
    rewrite (decL_w64u pad) by lia.
    rewrite (decL_w64u 2) by lia.
    try rewrite (wz c) by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold DEC_WSMASK, G_B64, DEC_CEIL, HEAD in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
- unfold sh_ok, decL_hSH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H Wc) memc E decL_Bx 20%nat (d_text d) (Z.of_nat (length (d_tb d)) + 1)
           (d_text d + Z.of_nat i) 0 1 HRA).
  + unfold decL_Bx. apply (U_atom E 21 SHADOW_OFF);
      [unfold E; rewrite (decL_E_reg d regsc _ 21 21%bv eq_refl), R21; reflexivity | unfold SHADOW_OFF; lia].
  + apply (U_atom E 20 (d_text d + Z.of_nat i));
      [unfold E; rewrite (decL_E_reg d regsc _ 20 20%bv eq_refl), R20; reflexivity | lia].
  + lia.
  + lia.
  + intros x Hx. cbn in Hx. destruct (T3 x ltac:(lia)) as (A1 & _). exact A1.
Qed.

End L1.
