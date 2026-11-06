(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:155-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbl.v:141-145 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-148, 156-160 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used
   under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_A.v, with its module paths and module names changed; 586 of its 646 lines of code are new or changed and 748 lines of the source are left out. *)
(* Segment ENTRY of the image-B walk of LLVMFuzzerTestOneInput (fuzz_codec.asan-ubsan 0x8099c-0x80c2c, 165
   instructions): the segment lemma seg_entry_holds of lib/AU/Prog/codec_bmain_inv.v. The structure is the image-A
   ENTRY walk (lib/A/Prog/codec_amain_entry_a.v and codec_amain_entry.v) at image B's code.
   - part a, the entry to the return of the class-3 frame request at 0x80a10 (be_r1):
     0x8099c .. 0x80a0c: the real frame 320 (`sd zero,0(sp)` and the thirteen saves at sp0 - 104 .. sp0 - 8),
     s0 = sp0, sp = s1 = sp1 = 32 * ((sp0 - 320) / 32) (0x809dc `andi sp,sp,-32`), s8 = n, s9 = p, the shadow offset
     into s5 through the .got slot 0x9e430 and its cell, the use-after-return cell through the .got slot 0x9e488 (it
     holds 1, so `beqz a2` at 0x80a04 is not taken), a0 = 480, jal 0x3d550: one run from the entry state (the
     journal of ajournal_init), then the class-3 frame request through CPgWalkFrameU.cpg_stack_malloc_keep_io;
   - part b, from 0x80a10 to the loop head 0x80c30 (be_p2):
     the state at 0x80a10: atoms 33 = the flag address FL, 34 = shadow_addr F; s5 pinned to the shadow offset (atom
     32); the frame (atom 10 = a0 = F, flag address at F + 504), its 64 shadow bytes (zero after the request) and the
     spill window 16(s1) .. 199(s1); the alias of (F >> 3) + s5 to atom 34 and of n >> 26 to 0 (n < 2 ^ 26);
     0x80a10 .. 0x80ba0: one run: `bnez s4` at 0x80a20 is taken (F >= 4096; the machine-stack fallback 0x80a24 ..
     0x80a3c is not reached), 176(s1) = F, the frame's description words, the 60 shadow stores (shm 0xf8), `beqz a0`
     at 0x80b78 is taken (n >> 26 = 0), the spills 80 / 104 / 72(s1), s6 = F + 32, s3 = F + 48, s7 = F + 192,
     s10 = F + 448;
     0x80ba0: check_personality through its image-B contract cdcU_check_pers_specX (CPgWalkCallU.cpw_call), its
     cimg_rd from the start-up facts (globs_marked / img_shadow_vis, the rows' freedom, the read-only image kept along
     the journal), the state re-seated at 0x80ba4 with the three regions kept (region_kept_tcj_frame / _stack);
     0x80ba4 .. 0x80c2c: one run: s4 = 0, in.p / in.n at 184 / 192(s1), s9 = F + 448, the spills 16 .. 152(s1),
     s10 = 1, s3 = sp1 + 216;
     at 0x80c30: mcommon read off the final state's regions and registers (the saves kept by the runs and the call,
     the input bytes by the journal), the cut inv_head g pos sp1 0 with the cursor at c = 0.
   The segment's range holds no UBSan trap edge (codec_bmain_inv.v's lists start at 0x80c4c). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YImgTopU.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YO09 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkKeptU CPgWalkFrameU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkImgU CPgWalkRoU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_lem codec_bmain_st.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- small arithmetic and memory facts ---------------------------------------------------------------------- *)
(* `andi x, y, -32` of an offset of an atom (the realignment of sp) *)
Lemma be_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
(* a field of a region whose chunk is an atom with a known value *)
Lemma be_fld : forall E m n bse cs lo hi wlo whi od (w : N) i v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal w (SOff i 0))) cs -> ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  Z.of_N w <= 8 ->
  val_mem tfibsegs m (bse + od) (N.to_nat w) v.
Proof.
intros E m n bse cs lo hi wlo whi od w i v Hr Hb Hc Hi Hv Hw.
eapply (field_of_region E m n bse cs lo hi wlo whi od w (SOff i 0) v Hr Hb Hc); [|exact Hv | exact Hw].
cbn [sv_denot]. rewrite Hi, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma be_regv : forall (x : word), x = Z_to_bv 64 (bv_unsigned x) /\ 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8).
Proof.
intros x. split; [symmetry; apply Z_to_bv_bv_unsigned|].
pose proof (bv_unsigned_in_range _ x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Ltac be_in := cbn [In]; repeat first [left; reflexivity | right].
(* n >> 26 of an input length below 2 ^ 26 *)
Lemma be_srl26 : forall E (m : nat) n, ew E m = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  sv_denot E (SAlu ALU_SRL (SOff m 0) (SLit 26)) = sv_denot E (SLit 0).
Proof.
intros E m n Hn Hr. rewrite (denot_lit_U E (SAlu _ _ _)), (denot_lit_U E (SLit 0)). f_equal.
rewrite U_SAlu, !U_SLit, U_SOff, Hn. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
rewrite Z.add_0_r, (zcanon_id n) by (unfold M64; lia). change (Z.land (zcanon 26) 63) with 26.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* the state at 0x80a10: the frame (atom 10), its shadow (atom 34), the spill window 16(s1) .. 199(s1) (atom 9) *)
Definition be_rs2 : smem :=
  [cw_frame_region 10 33 3; cw_fshadow_region 34 3; YP09.mkRegion (Some 9%nat) 16 200 16 200 []].
Definition be_G2 : facts :=
  mkFacts [(10%nat, HPTR 6); (33%nat, HPTR 0); (34%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3);
           (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0);
           (24%nat, mkAF 0 (2 ^ 26 - 1) 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0), SOff 34 0);
     (SAlu ALU_SRL (SOff 24 0) (SLit 26), SLit 0)].

(* the write windows of part b's states: the frame (atom 10), its shadow (atom 34), the spill window (atom 9) *)
Ltac be_awr :=
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ownv =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ownv) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 3 _ 10%nat);
      [reflexivity | eassumption | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 3) with 512; lia |]
  | eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 _ 34%nat);
      [reflexivity | eassumption | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 3 / 8) with 64; lia |]
  | lazymatch goal with U9 : bv_unsigned (ew _ 9) = ?s1 |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (s1 - s0));
      [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |] end ].
Ltac be_kwr :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
     repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hb end;
     repeat match goal with H : frame_addr _ _ _ = _ |- _ => rewrite H in Hb end;
     lia | ]);
  destruct Hr.

(* the 33 string rows: in a read-only segment, inside the image's read range, below the read window's end *)
Lemma be_rows_ok : forallb (fun r => bm_ro_b (fst r) (snd r) && (0 <? snd r) && (IMG_LO + 64 <=? fst r) &&
  (fst r + snd r + 64 <=? IMG_HI) && (fst r + snd r <=? CB_RHI)) CB_ROSTRS = true.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* the realigned sp of the machine frame *)
Definition be_sp1 (g : ectx) : Z := 32 * ((e_sp0 g - 320) / 32).
(* the thirteen saved words of the prologue, as mcommon states them *)
Definition be_saves (g : ectx) (W : world tfibsegs) (mem2 : word -> option byte) : Prop :=
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 8) 8 (raZ (e_regs g)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 16) 8 (bv_unsigned (getr (e_regs g) 8)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)).
(* the saves keep their values when their bytes do *)
Lemma be_saves_kept : forall g (W W' : world tfibsegs) m m',
  (forall a, e_sp0 g - 104 <= a < e_sp0 g -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  be_saves g W m -> be_saves g W' m'.
Proof.
intros g W W' m m' HK (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
assert (KV : forall o v, 8 <= o <= 104 -> val_mem tfibsegs (mrestrict (w_H W) m) (e_sp0 g - o) 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') m') (e_sp0 g - o) 8 v).
{ intros o v Ho Hv. apply (cw_val_mem_kept (w_H W) (w_H W') m m'); [|exact Hv].
  intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. apply HK. lia. }
split; [exact (KV 8 _ ltac:(lia) S1)|]. split; [exact (KV 16 _ ltac:(lia) S2)|].
split; [exact (KV 24 _ ltac:(lia) S3)|]. split; [exact (KV 32 _ ltac:(lia) S4)|].
split; [exact (KV 40 _ ltac:(lia) S5)|]. split; [exact (KV 48 _ ltac:(lia) S6)|].
split; [exact (KV 56 _ ltac:(lia) S7)|]. split; [exact (KV 64 _ ltac:(lia) S8)|].
split; [exact (KV 72 _ ltac:(lia) S9)|]. split; [exact (KV 80 _ ltac:(lia) S10)|].
split; [exact (KV 88 _ ltac:(lia) S11)|]. split; [exact (KV 96 _ ltac:(lia) S12)|].
exact (KV 104 _ ltac:(lia) S13).
Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.

(* 0x80a10, the request's return: the journal from the entry with the new frame (3, pos) as own, the frame's shadow
   zero, the flag address at F + 504, a0 = F, the registers the rest of the segment reads, the saves *)
Definition be_r1 (g : ectx) : world tfibsegs -> config -> Prop :=
  fun W2 c2 => W2 = e_W g /\ exists S2 regs2 mem2 md2 pos,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x80a10) mem2 (seg_rom tfibsegs)) md2 /\
    ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
      (e_ly g) S2 (e_W g) mem2 md2 0 /\
    frames S2 = [(3, pos)] /\ (exists f, S2 = set_fs f (e_S g)) /\ blocks_bytes S2 = blocks_bytes (e_S g) /\
    zero_shadow (aview tfibsegs (w_H (e_W g)) mem2) SHADOW_OFF (FA g pos) 512 /\
    rdword (aview tfibsegs (w_H (e_W g)) mem2) (FA g pos + 504) = Some (flag_addr (e_ly g) 3 pos) /\
    getr regs2 10 = w64 (FA g pos) /\
    getr regs2 2 = w64 (be_sp1 g) /\ getr regs2 9 = w64 (be_sp1 g) /\ getr regs2 8 = w64 (e_sp0 g) /\
    getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\ getr regs2 21 = w64 SHADOW_OFF /\
    getr regs2 24 = w64 (e_n g) /\ getr regs2 25 = w64 (e_p g) /\
    be_saves g (e_W g) mem2.

Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Hypothesis RF : cpw_rows_free B CB_ROSTRS.
Hypothesis CPERS : cdcU_check_pers_specX tfibsegs B MT CB_RLO CB_RHI CB_PERS CB_ROSTRS BM_check_pers.
Hypothesis ASM3 : astack_malloc_realizes tfibsegs B 3.
Hypothesis SMP : stack_malloc_progressP B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.

(* ================================ part a: the entry to the frame request's return ================================ *)
Lemma be_p1 : forall g, e_pre B MT K XM_LIB g ->
  SRr tfibsegs (e_W g) (cfg_at tfibsegs A_LLVMF (e_regs g) (e_mem g) (e_md g)) (be_r1 g).
Proof.
intros g Hpre. destruct g as [ly S W mem md regs p n pl M].
unfold be_r1, be_saves, be_sp1, FA, e_sp0. cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M].
unfold e_pre, codec_lib_pre_x in Hpre. cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M] in Hpre.
destruct Hpre as (HFN & Hra & Ha0 & Ha1 & Hpn & _ & _ & Hfr0 & _ & _ & _).
pose proof HFN as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & _ & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (ajournal_init tfibsegs B LLVMF_STK [] ly S W regs mem md [] HFN) as HJ.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : LLVMF_STK = 32768) by reflexivity.
assert (Hpres' : forall a, spZ regs - 320 <= a < spZ regs -> apresent (w_H W) mem a)
  by (intros a Ha; apply Hpres; lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (cw_entry B TL LAWS A_LLVMF 320 [] [uar_got_region; uar_cell_region] [] ly S W regs mem md HAR
  ltac:(lia) ltac:(lia) Hal16 Hpres' ltac:(vm_compute; reflexivity)) as HS.
set (E := Ereg regs (cw_extra [])) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
specialize (HS ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold region_ok, uar_got_region, uar_cell_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  unfold A_GOT_uar, A_uar_glob; (split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]);
  apply Forall_cons; try apply Forall_nil;
  first
  [ apply (chunk_ok_val tfibsegs E _ 0 0x9e488 8 (SLit 0xa6dc0) 0xa6dc0); [reflexivity | zside | zside |];
    rewrite Z.add_0_l; exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kguar)
  | apply (chunk_ok_val tfibsegs E _ 0 0xa6dc0 4 (SLit 1) 1); [reflexivity | zside | zside |];
    rewrite Z.add_0_l; exact (val_mem_of_rd32 tfibsegs (w_H W) mem _ _ Kuar) ])).
specialize (HS ltac:(apply pairwise_disjoint_of_extents;
  unfold cw_regs, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [base_val]; rewrite Usp;
  unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia)).
specialize (HS I).
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) mem)) by constructor.
assert (B2 := Usp).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E2v : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
clearbody E.
unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 0x8099c).
(* 0x8099c .. jal 0x3d550 at 0x80a0c: one run, stopped at the request *)
cw_run_to cw_awr_stk 0x3d550.
clear_frames.
(* the registers and the saves at the request *)
set (sp1 := 32 * ((spZ regs - 320) / 32)).
destruct (sp1_facts (spZ regs - 320) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 336 <= sp1 <= spZ regs - 320) by lia. clear Hsp1r.
assert (Dand : sv_denot E (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32))) = Z_to_bv 64 sp1)
  by exact (be_denot_and_m32 E 2 (spZ regs) (-320) E2v ltac:(lia) ltac:(lia) ltac:(unfold spZ in *; lia)).
assert (Dadd : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 sp1).
{ change (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32))) (SLit 0)))
    with (alu64 ALU_ADD (sv_denot E (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32)))) (sv_denot E (SLit 0))).
  rewrite Dand. cbn [sv_denot]. rewrite YI08.alu64_add_lit, Z.add_0_r. reflexivity. }
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) Dand R2.
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1) Dadd R9.
rreg HS (1%bv : bv 5) R1. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (8%bv : bv 5) R8.
rreg HS (21%bv : bv 5) R21. rreg HS (24%bv : bv 5) R24. rreg HS (25%bv : bv 5) R25.
clear Dand Dadd.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RG0.
cbn [ms_mem restrict] in RG0.
assert (VS : forall (i : nat) (r : bv 5) od, Z.of_nat i = bv_unsigned r ->
   In (YP09.mkChunk od (CVal 8 (SOff i 0)))
     [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
      YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
      YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
      YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
      YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
      YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
      YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
   val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 (bv_unsigned (getr regs r))).
{ intros i r od Hir Hc. rewrite <- Usp.
  lazymatch type of RG0 with region_ok _ _ _ ?rg =>
    let rg' := eval vm_compute in rg in change rg with rg' in RG0 end.
  eapply (be_fld E _ 2 _ _ _ _ _ _ od 8%N i (bv_unsigned (getr regs r)) RG0 eq_refl);
  [ cbn [In] in Hc; repeat (destruct Hc as [Hc | Hc]; [rewrite <- Hc; be_in |]); destruct Hc
  | rewrite (EE i r Hir); exact (proj1 (be_regv _)) | exact (proj2 (be_regv _)) | lia ]. }
pose proof (VS 1%nat 1%bv (-8) eq_refl ltac:(be_in)) as V1.
pose proof (VS 8%nat 8%bv (-16) eq_refl ltac:(be_in)) as V8.
pose proof (VS 9%nat 9%bv (-24) eq_refl ltac:(be_in)) as V9.
pose proof (VS 18%nat 18%bv (-32) eq_refl ltac:(be_in)) as V18.
pose proof (VS 19%nat 19%bv (-40) eq_refl ltac:(be_in)) as V19.
pose proof (VS 20%nat 20%bv (-48) eq_refl ltac:(be_in)) as V20.
pose proof (VS 21%nat 21%bv (-56) eq_refl ltac:(be_in)) as V21.
pose proof (VS 22%nat 22%bv (-64) eq_refl ltac:(be_in)) as V22.
pose proof (VS 23%nat 23%bv (-72) eq_refl ltac:(be_in)) as V23.
pose proof (VS 24%nat 24%bv (-80) eq_refl ltac:(be_in)) as V24.
pose proof (VS 25%nat 25%bv (-88) eq_refl ltac:(be_in)) as V25.
pose proof (VS 26%nat 26%bv (-96) eq_refl ltac:(be_in)) as V26.
pose proof (VS 27%nat 27%bv (-104) eq_refl ltac:(be_in)) as V27.
clear VS RG0.
(* 0x3d550: the class-3 frame request *)
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 251216 with (pc_stack_malloc (as_code B) 3) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (cpg_stack_malloc_keep_io tfibsegs B LAWS Hsegs errno_low ML SMP 3 ASM3 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - rewrite Hfr0. apply Z.ltb_lt. vm_compute. reflexivity. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0' & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz
  & Hflag & HKa & HSf & HKr & Hio).
replace (spZ regs + (sp1 - spZ regs) - ESTACK) with (sp1 - 4096) in HKa by (unfold ESTACK; lia).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HKa by lia.
assert (CS : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a) by exact (proj1 HKa).
assert (KS : forall od vv, -104 <= od <= -8 ->
   val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 vv ->
   val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - - od) 8 vv).
{ intros od vv Hod Hvv. replace (spZ regs - - od) with (spZ regs + od) by lia.
  apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem ms) mem2 (spZ regs + od) 8 vv); [|exact Hvv].
  intros x Hx. apply KA; [cbn in Hx; lia | lia]. }
apply SRr_ret. split; [reflexivity|].
exists S2, regs2, mem2, md2, pos.
split; [reflexivity|].
split; [exact HJ2|].
split; [rewrite Hfrs2, Hfr0; reflexivity|].
split; [exact HSf|].
split; [exact Hbb2|].
split; [change (fs_frame_bytes 3) with 512 in Hz; exact Hz|].
split; [change (fs_frame_bytes 3) with 512 in Hflag; replace (frame_addr ly 3 pos + 512 - 8) with (frame_addr ly 3 pos + 504) in Hflag by lia; exact Hflag|].
split; [exact Ha0'|].
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (CS 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (CS 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (CS 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (CS 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (CS 9 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (CS 21 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (CS 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (CS 25 ltac:(unfold acallee_saved; lia)).
split; [rewrite P2; exact R2|].
split; [rewrite P9; exact R9|].
split; [rewrite P8, R8, E2v; reflexivity|].
split; [rewrite P3, R3; exact (EE 3%nat 3%bv eq_refl) || (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp)|].
split; [rewrite P4, R4; exact (EE 4%nat 4%bv eq_refl) || (rewrite (EE 4%nat 4%bv eq_refl); exact Htp)|].
split; [rewrite P21, R21, E32; reflexivity|].
split; [rewrite P24, R24, (EE 11%nat 11%bv eq_refl); exact Ha1|].
split; [rewrite P25, R25, (EE 10%nat 10%bv eq_refl); exact Ha0|].
split; [exact (KS (-8) _ ltac:(lia) V1)|].
split; [exact (KS (-16) _ ltac:(lia) V8)|].
split; [exact (KS (-24) _ ltac:(lia) V9)|].
split; [exact (KS (-32) _ ltac:(lia) V18)|].
split; [exact (KS (-40) _ ltac:(lia) V19)|].
split; [exact (KS (-48) _ ltac:(lia) V20)|].
split; [exact (KS (-56) _ ltac:(lia) V21)|].
split; [exact (KS (-64) _ ltac:(lia) V22)|].
split; [exact (KS (-72) _ ltac:(lia) V23)|].
split; [exact (KS (-80) _ ltac:(lia) V24)|].
split; [exact (KS (-88) _ ltac:(lia) V25)|].
split; [exact (KS (-96) _ ltac:(lia) V26)|].
exact (KS (-104) _ ltac:(lia) V27).
Qed.

(* ================================ check_personality's image ranges ================================ *)
(* the personalities and the 33 string rows, from the start-up facts *)
Lemma be_cimg : forall (W : world tfibsegs) memc sp T,
  arodata_ok B (aview tfibsegs (w_H W) memc) -> CB_RHI <= sp - T ->
  cimg_rd tfibsegs B CB_RLO CB_RHI W memc sp T ((CB_PERS, 48) :: CB_ROSTRS).
Proof.
intros W memc sp T HR Hwin.
assert (U : forall q sz a n, In (q, sz) CODEC_GLOBS -> q <= a -> a + n <= q + sz -> 0 < n ->
  IMG_LO + 64 <= a -> a + n + 64 <= IMG_HI -> cimg_usable tfibsegs B a n).
{ intros q sz a n Hin Hqa Han Hn Hlo Hhi ly' S' W' mem' md' HAR.
  split; [exact (ro_usable_glob tfibsegs B CODEC_GLOBS ly' S' W' mem' md' q sz a n GM Hin HAR Hqa Han)|].
  intros _. exact (ro_hull tfibsegs B ly' S' W' mem' md' a n IV HAR Hn Hlo Hhi). }
split; [intros a Ha; exact (HR a Ha)|].
apply Forall_cons.
- cbn [fst snd]. split.
  + intros i Hi. right. unfold CB_PERS, CB_RLO, CB_RHI. lia.
  + unfold cimg_range.
    split; [unfold CB_PERS; lia|]. split; [lia|]. split; [unfold CB_PERS; lia|].
    split; [left; unfold CB_PERS, kLowMemEnd; lia|].
    split; [left; unfold CB_PERS, CB_RHI in *; lia|].
    split.
    * intros x Hx. split; [|exact (tl_lib_consts B TL x ltac:(unfold lib_const_addr; unfold CB_PERS in Hx; lia))].
      unfold in_img. eexists. split; [right; right; left; reflexivity|].
      match goal with |- Z.le ?lo x /\ Z.lt x (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
        change lo with l; change sz with h end.
      unfold CB_PERS in Hx. lia.
    * apply (U CB_PERS 48); [exact cg_PERS | lia | lia | lia | cbv [IMG_LO CB_PERS]; lia | cbv [IMG_HI IMG_TOP CB_PERS]; lia].
- apply Forall_forall. intros [q sz] Hin.
  pose proof (proj1 (forallb_forall _ _) be_rows_ok (q, sz) Hin) as Hb. cbv beta in Hb. cbn [fst snd] in Hb |- *.
  apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3].
  apply andb_prop in Hb as [Hro H2].
  apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
  assert (Hgl : In (q, sz) CODEC_GLOBS) by exact (proj1 (Forall_forall _ _) CB_ROSTRS_globs (q, sz) Hin).
  split.
  + intros i Hi. apply (bm_in_ro q sz Hro). lia.
  + cbv [IMG_LO IMG_HI IMG_TOP CB_RHI] in H3, H4, H5, Hwin.
    unfold cimg_range.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [left; unfold kLowMemEnd; lia|].
    split; [left; lia|].
    split.
    * intros x Hx. split.
      -- pose proof Hro as Hro'. unfold bm_ro_b in Hro'. apply existsb_exists in Hro' as (s & Hs & Hc).
         apply andb_prop in Hc as (Hc & Hhi). apply andb_prop in Hc as (_ & Hlo).
         apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
         unfold in_img. exists s. split; [exact Hs | lia].
      -- destruct (cpw_rows_free_In B CB_ROSTRS q sz (x - q) RF Hin ltac:(lia)) as (Ho & He).
         replace (q + (x - q)) with x in Ho, He by lia. exact (conj Ho He).
    * apply (U q sz); [exact Hgl | lia | lia | lia | cbv [IMG_LO]; lia | cbv [IMG_HI IMG_TOP]; lia].
Qed.

(* ================================ part b: the request's return to the loop head ================================ *)
Lemma be_p2 : forall g W2 c2, e_pre B MT K XM_LIB g -> be_r1 g W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => exists pos sp1, inv_head B MT K XM_LIB g pos sp1 0 W3 c3).
Proof.
intros g W2 c2 Hpre Hr1.
destruct Hr1 as (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ & Hfrs2 & HSf & Hbb2 & Hz & Hflag & R10 & R2 & R9 & R8
  & R3 & R4 & R21 & R24 & R25 & HSV).
unfold be_sp1 in R2, R9.
pose proof Hpre as HPRE. unfold e_pre, codec_lib_pre_x in HPRE.
destruct HPRE as (HFN & _ & Ha0 & Ha1 & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & _).
pose proof HFN as (HAR0 & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (e_regs g)) with (e_sp0 g) in Hal16, Hslo, Hshi.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : LLVMF_STK = 32768) by reflexivity.
assert (TCP : TB_check_pers = 8272) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 pos HAR2 Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B _ _ _ _ _ 3 pos HAR2 Hin) as (HF64 & _ & _).
destruct (FFL _ _ _ _ _ 3 pos HAR2 Hin) as (_ & _ & _ & (HFL4096 & _ & HFLc)).
change (fs_frame_bytes 3) with 512 in HFceil, HFapp, Hz.
unfold FA in *.
set (F := frame_addr (e_ly g) 3 pos) in *.
set (FL := flag_addr (e_ly g) 3 pos) in *.
set (sp1 := 32 * ((e_sp0 g - 320) / 32)) in *.
destruct (sp1_facts (e_sp0 g - 320) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : e_sp0 g - 336 <= sp1 <= e_sp0 g - 320) by lia. clear Hsp1r.
assert (Hn26 : 0 <= e_n g < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn _]]; lia).
assert (HF0 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8 : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
(* the start state *)
set (E := Ereg regs2 (cw_extra [FL; shadow_addr F])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 FL) by (subst E; exact (cw_ew_x regs2 [FL; shadow_addr F] 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr F)) by (subst E; exact (cw_ew_x regs2 [FL; shadow_addr F] 1)).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E24 : ew E 24 = Z_to_bv 64 (e_n g)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr F)
  by (rewrite E34; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok tfibsegs E (mkSS 0x80a10 (sr_set sr_atoms 21%bv (SOff 32 0)) be_rs2 None be_G2)
  (restrict (w_H (e_W g)) (mkst regs2 (Z_to_bv 64 0x80a10) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra [FL; shadow_addr F])) with E.
  - apply regs_ok_pin; [subst E; apply regs_ok_Ereg | intros Hx; discriminate Hx |].
    rewrite R21. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - vm_compute. reflexivity.
  - unfold be_rs2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (cw_frame_region_ok B LAWS FFL _ 10 33 (e_ly g) S2 (e_W g) mem2 md2 3 pos HAR2 Hin E10 E33).
      change (fs_frame_bytes 3) with 512. fold F FL. replace (F + 512 - 8) with (F + 504) by lia. exact Hflag.
    + apply (cw_fshadow_region_ok B LAWS _ 34 (e_ly g) S2 (e_W g) mem2 md2 3 pos HAR2 Hin E34).
      change (fs_frame_bytes 3) with 512. exact Hz.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable tfibsegs). apply HJpres. lia.
  - apply pairwise_disjoint_of_extents. unfold be_rs2, cw_frame_region, cw_fshadow_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (fs_frame_bytes 3) with 512. change (512 / 8) with 64.
    rewrite U10, U34, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8b.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *. repeat split; lia.
  - split; [|split; [exact I|]].
    + destruct (cw_frame_afacts B LAWS E 10 33 34 (e_ly g) S2 (e_W g) mem2 md2 3 pos FFL HAR2 Hin E10 E33 E34)
        as (A10 & A33 & A34).
      unfold be_G2. cbn [f_atoms atoms_ok]. split; [exact A10|]. split; [exact A33|]. split; [exact A34|].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, E32, E24, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
    + unfold be_G2. cbn [f_alias alias_ok]. split; [|split; [|exact I]].
      * exact (shadow_decl_ok E 10%nat 32%nat 34%nat F SB E10 ltac:(lia) E32 E34).
      * exact (be_srl26 E 24 (e_n g) E24 Hn26). }
clearbody E.
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((F <= a < F + 512) \/ (shadow_addr F <= a < shadow_addr F + 64) \/ (sp1 + 16 <= a < sp1 + 200)) ->
  aview tfibsegs (w_H (e_W g)) mem2 a = aview tfibsegs (w_H (e_W g)) mem2 a) by (intros; reflexivity).
(* 0x80a10 .. jal 0x8391c at 0x80ba0: one plain run (no instrumented check on the way) *)
aj_run_to tfibtbl_lib_ok HS HJ 0x8391c; [be_awr|].
cw_keep be_kwr.
(* the saves at the call *)
assert (HSV1 : be_saves g (e_W g) (ms_mem ms)).
{ apply (be_saves_kept g (e_W g) (e_W g) mem2 (ms_mem ms)); [|exact HSV].
  intros a Ha. apply KE; [lia|]. pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8b.
  unfold shadow_addr, SHADOW_OFF. lia. }
clear KE.
(* 0x8391c: check_personality through its contract *)
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4.
assert (Esp : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; lia).
assert (HRO : arodata_ok B (aview tfibsegs (w_H (e_W g)) (ms_mem ms)))
  by exact (arodata_ok_at B MT K XM_LIB g _ _ _ _ _ _ _ Hpre HJ).
eapply (cpw_call (e_W g) E _ ms _ _ _ HS eq_refl).
{ eapply CPERS.
  - eapply (cpw_entry B).
    + exact HJ.
    + rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
    + rewrite Q3, (EE 3%nat 3%bv eq_refl). exact R3.
    + rewrite Q4, (EE 4%nat 4%bv eq_refl). exact R4.
    + rewrite Esp. exact Hsp1al16.
    + rewrite Esp, TCP. lia.
    + rewrite Esp. lia.
    + unfold EV_CDC, EV_LIB in *. lia.
    + apply Permutation_refl.
    + rewrite Hbb2. unfold LIVE_CDC, LIVE_LIB in *. lia.
  - apply be_cimg; [exact HRO | rewrite Esp, TCP; unfold CB_RHI; lia]. }
cbv beta. intros W3 c3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & HPerm3 & HIO3 & HMLE3 & KT3 & _).
rewrite Q1. rewrite Esp in KT3.
(* the saves after the call *)
assert (HSV3 : be_saves g W3 mem3).
{ apply (be_saves_kept g (e_W g) W3 (ms_mem ms) mem3); [|exact HSV1].
  intros a Ha. pose proof KT3 as (K1 & _). apply K1; [lia | lia | intros Hx; exact Hx]. }
(* the frame after the call *)
pose proof HJ3 as (HAR3 & Hly3 & _).
assert (Hin3 : In (3, pos) (frames S3)) by (rewrite Hfrs3; exact Hin).
assert (EF3 : frame_addr ly3 3 pos = F) by (unfold F, frame_addr; destruct Hly3 as (_ & _ & _ & _ & _ & EFl & _); lia).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 3 pos HAR3 Hin3) as (_ & _ & Hpr3 & Hsh3).
rewrite EF3 in Hpr3, Hsh3. change (fs_frame_bytes 3) with 512 in Hpr3, Hsh3. change (512 / 8) with 64 in Hsh3.
(* the state re-seated at 0x80ba4: the frame, its shadow and the spill window kept *)
lazymatch type of HS with st_ok _ _ ?ssv _ =>
  let Kv := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
  jafter_call_keep HS Kv regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS2 end.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_tcj_frame B E _ _ _ _ _ _ _ _ _ 10%nat _ _ _ _ _ F 3 pos KT3 U10 Hin).
    + left. change (fs_frame_bytes 3) with 512. fold F. lia.
    + intros a Ha Hx. exact Hx.
    + intros a Ha. exact (proj1 (Hpr3 a ltac:(lia))).
  - eapply (region_kept_tcj_frame B E _ _ _ _ _ _ _ _ _ 34%nat _ _ _ _ _ (shadow_addr F) 3 pos KT3 U34 Hin).
    + right. change (fs_frame_bytes 3 / 8) with 64. fold F. lia.
    + intros a Ha Hx. exact Hx.
    + intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by lia.
      exact (proj1 (Hsh3 (a - shadow_addr F) ltac:(lia))).
  - eapply (region_kept_tcj_stack B E _ _ _ _ _ _ _ _ _ 9%nat _ _ _ _ _ sp1 KT3 U9).
    + intros a Ha. split; [lia|]. split; [lia | intros Hx; exact Hx].
    + intros a Ha. split; lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?En _ _ => remember En as E' eqn:HE' in HS end.
assert (EE' : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regs2 r)
  by (intros nn r Hnl Hnn; rewrite HE', ew_havoc_old by lia; apply EE; exact Hnn).
assert (E32' : ew E' 32 = Z_to_bv 64 SB) by (rewrite HE', ew_havoc_old by lia; exact E32).
assert (E33' : ew E' 33 = Z_to_bv 64 FL) by (rewrite HE', ew_havoc_old by lia; exact E33).
assert (E34' : ew E' 34 = Z_to_bv 64 (shadow_addr F)) by (rewrite HE', ew_havoc_old by lia; exact E34).
assert (E10' : ew E' 10 = Z_to_bv 64 F) by (rewrite HE', ew_havoc_old by lia; exact E10).
assert (E2' : ew E' 2 = Z_to_bv 64 sp1) by (rewrite HE', ew_havoc_old by lia; exact E2).
assert (E9' : ew E' 9 = Z_to_bv 64 sp1) by (rewrite HE', ew_havoc_old by lia; exact E9).
assert (E24' : ew E' 24 = Z_to_bv 64 (e_n g)) by (rewrite HE', ew_havoc_old by lia; exact E24).
assert (U10' : bv_unsigned (ew E' 10) = frame_addr ly3 3 pos) by (rewrite EF3, E10'; apply unsigned_lit_small; lia).
assert (U34' : bv_unsigned (ew E' 34) = shadow_addr (frame_addr ly3 3 pos))
  by (rewrite EF3, E34'; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (U9' : bv_unsigned (ew E' 9) = sp1) by (rewrite E9'; apply unsigned_lit_small; lia).
assert (U10F : bv_unsigned (ew E' 10) = F) by (rewrite E10'; apply unsigned_lit_small; lia).
assert (U34F : bv_unsigned (ew E' 34) = shadow_addr F)
  by (rewrite E34'; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
clear HE' EE E32 E33 E34 E10 E2 E9 E24 U10 U34 U9 U2 Q1 Q2 Q3 Q4.
clear KT3 HSV1 HRO HJ HP3 Esp. clear ms.
change (0 + EV_CDC) with 0 in HJ3.
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((F <= a < F + 512) \/ (shadow_addr F <= a < shadow_addr F + 64) \/ (sp1 + 16 <= a < sp1 + 200)) ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a) by (intros; reflexivity).
(* 0x80ba4 .. 0x80c2c: one plain run to the loop head *)
aj_run_to tfibtbl_lib_ok HS HJ3 0x80c30; [be_awr|].
cw_keep be_kwr.
(* the final state at 0x80c30 *)
assert (HSVf : be_saves g W3 (ms_mem ms)).
{ apply (be_saves_kept g W3 W3 mem3 (ms_mem ms)); [|exact HSV3].
  intros a Ha. apply KE; [lia|]. pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8b.
  unfold shadow_addr, SHADOW_OFF. lia. }
destruct (cw_frame_start MT MTL MTF B (e_ly g) (e_S g) S2 HSf) as (P1 & M1).
destruct (cw_frame_step MT MTL B (e_ly g) (e_S g) (e_ly g) S2 ly3 S3 P1 M1 HPerm3 HMLE3) as (P3 & M3).
rreg HS (2%bv : bv 5) G2. rreg HS (9%bv : bv 5) G9. rreg HS (8%bv : bv 5) G8. rreg HS (3%bv : bv 5) G3.
rreg HS (4%bv : bv 5) G4. rreg HS (20%bv : bv 5) G20. rreg HS (18%bv : bv 5) G18. rreg HS (21%bv : bv 5) G21.
rreg HS (23%bv : bv 5) G23. rreg HS (25%bv : bv 5) G25. rreg HS (19%bv : bv 5) G19. rreg HS (27%bv : bv 5) G27.
rreg HS (26%bv : bv 5) G26.
pose proof (st_ok_region_nth E' _ _ 0 _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth E' _ _ 1 _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth E' _ _ 2 _ HS eq_refl) as RG2.
cbn [ms_mem restrict] in RG0, RG1, RG2.
lazymatch type of RG0 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG0 end.
lazymatch type of RG2 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG2 end.
lazymatch type of RG1 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG1 end.
assert (Hp63 : 0 <= e_p g < 2 ^ 63).
{ destruct Hpn as [[_ ->] | [Hn Hb]]; [unfold A_EMPTY; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hb) as (_ & H4096 & Hbc & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq). lia. }
(* the spills, from the final spill window *)
assert (SPL : forall od e v, In (YP09.mkChunk od (CVal 8 e)) (YP09.r_chunks
    ltac:(lazymatch type of RG2 with region_ok _ _ _ ?rg => exact rg end)) ->
  sv_denot E' e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (sp1 + od) 8 v).
{ intros od e v Hc He Hv.
  exact (field_of_region E' _ 9%nat sp1 _ _ _ _ _ od 8%N e v RG2 U9' Hc He ltac:(zside) ltac:(zside)). }
assert (DF : forall o, 0 <= o <= 512 -> sv_denot E' (SOff 10 o) = Z_to_bv 64 (F + o))
  by (intros o Ho; cbn [sv_denot]; rewrite E10', unsigned_lit_small by lia; reflexivity).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. exists pos, sp1.
unfold inv_head, mcut.
exists ly3, S3, (ms_regs ms), (ms_mem ms). eexists. exists 0.
split; [reflexivity|].
split; [exact HJ3|].
split; [rewrite Hfrs3; exact Hfrs2|].
split; [unfold EV_LIB; lia|].
split; [exact M3|].
split.
{ unfold mcommon, FA. fold F.
  split; [exact Hpre|].
  split; [reflexivity|].
  split; [rewrite G2, E2'; reflexivity|].
  split; [rewrite G9, E9'; reflexivity|].
  split; [rewrite G8, (EE' 8%nat 8%bv ltac:(lia) eq_refl); exact R8|].
  split; [rewrite G3, (EE' 3%nat 3%bv ltac:(lia) eq_refl); exact R3|].
  split; [rewrite G4, (EE' 4%nat 4%bv ltac:(lia) eq_refl); exact R4|].
  split; [rewrite G21, E32'; reflexivity|].
  split; [rewrite G18, E34'; reflexivity|].
  split; [rewrite G27; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
  split; [rewrite G23, E10', unsigned_lit_small by lia; reflexivity|].
  split; [rewrite G25, E10', unsigned_lit_small by lia; reflexivity|].
  split; [rewrite G19, E9', unsigned_lit_small by lia; reflexivity|].
  split; [rewrite G26; reflexivity|].
  split; [exact HF64|].
  split; [apply (SPL 16 (SOff 10 239)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 24 (SOff 10 336)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 32 (SOff 10 50)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 40 (SOff 10 340)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 48 (SLit 2448)); [be_in | reflexivity | lia]|].
  split; [apply (SPL 56 (SLit 23728)); [be_in | reflexivity | lia]|].
  split; [apply (SPL 64 (SOff 10 48)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 72 (SOff 10 0)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 80 (SOff 10 0)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 88 (SOff 10 34)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 96 (SOff 10 33)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 104 (SOff 10 80)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 112 (SOff 10 32)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 120 (SOff 10 232)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 128 (SOff 10 448)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 136 (SOff 10 360)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 144 (SOff 10 300)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 152 (SOff 10 268)); [be_in | rewrite DF by lia; f_equal; lia | lia]|].
  (* the saves *)
  destruct HSVf as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
  do 13 (split; [eassumption|]).
  (* the flag word *)
  split; [exact (be_fld E' _ 10 _ _ _ _ _ _ 504 8%N 33%nat FL RG0 U10F ltac:(be_in) E33' ltac:(zside) ltac:(zside))|].
  (* the frame's shadow bytes *)
  split.
  { intros i Hi. rewrite <- bm_shm8_eq.
    apply (bm_sh_read_all E' W3 (ms_mem ms) _ (shadow_addr F) bm_shm8 RG1).
    - cbn [YP09.r_base base_val]. exact U34F.
    - vm_compute. reflexivity.
    - rewrite bm_shm8_eq, bm_shm_len. lia. }
  (* the input bytes, kept by the journal *)
  split.
  { pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    intros j Hj. pose proof Hj as Hj'. rewrite length_map in Hj'.
    destruct (HPL j Hj) as (Hv & Hr). split; [|exact Hr].
    assert (Hn0 : 0 < e_n g) by lia.
    assert (Hin0 : In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)))
      by (destruct Hpn as [[Hz0 _] | [_ Hb]]; [lia | exact Hb]).
    assert (Hinb3 : In (e_p g, e_n g) (ablocks B ly3 S3))
      by (eapply Permutation_in; [apply Permutation_sym; exact P3 | exact Hin0]).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
    apply (cw_val_mem_kept (w_H (e_W g)) (w_H W3) (e_mem g) (ms_mem ms)); [|exact Hv].
    intros x Hx. cbn [Z.of_nat] in Hx.
    replace x with (e_p g + (x - e_p g)) by lia.
    apply (F2 (e_p g) (e_n g) (x - e_p g) Hin0 Hinb3); [lia | apply inFP_nil]. }
  exact P3. }
(* the loop counter and the cursor *)
split; [split; [lia | exact G20]|].
exists 0. split; [lia|].
split.
- apply (SPL 184 (SOff 25 0)); [be_in | | lia].
  cbn [sv_denot]. rewrite (EE' 25%nat 25%bv ltac:(lia) eq_refl), R25. unfold w64.
  rewrite unsigned_lit_small by lia. f_equal; lia.
- apply (SPL 192 (SOff 24 0)); [be_in | | lia].
  cbn [sv_denot]. rewrite E24', unsigned_lit_small by lia. f_equal; lia.
Qed.

(* ENTRY 0x8099c-0x80c2c: the segment lemma of codec_bmain_inv.v *)
Theorem seg_entry_holds : seg_entry B MT K XM_LIB.
Proof.
intros g W2 c2 (-> & ->) Hpre.
eapply SRr_bind; [exact (be_p1 g Hpre)|].
intros W3 c3 _ H3. exact (be_p2 g W3 c3 Hpre H3).
Qed.
End b.
End a.
