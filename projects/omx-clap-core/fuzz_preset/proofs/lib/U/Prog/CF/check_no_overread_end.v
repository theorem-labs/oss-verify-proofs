From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memcpy_c memset_c same_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_parse_c pj_free_c parse_noting_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_glue check_no_overread_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_spec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_ran_out_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* Phase C of check_no_overread (#102 ubsan entry 0x13868, frame 240): from the first pj_free call (0x16340, ra
   0x139d8) through pj_free of the trees at sp + 0x70, sp + 0x38, sp, free (0x18250) of the three copies s0, s1, s2,
   a0 = s3 = 0 and the epilogue (0x13a00 .. 0x13a2c).  g_ran_out and g_own_ran_out keep their entry bytes 0 along the
   frame invariant cj (cj_gro, cj_own). *)

Ltac cnoC_ret := unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Section Ph.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis HMAL : ms_malloc B = 0x18390.
Hypothesis HFREE : ms_free B = 0x18250.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Hypothesis MALLOC : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @free_contract_r fx rc B API F.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis MEMSET : memset_contract.
Hypothesis PARSE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @parse_noting_contract fx rc B API F.
Hypothesis PJFREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @pj_free_contract fx rc B API F.
Hypothesis SAME : same_contract.
Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE0 : call_pre_k B MR CNO_K L0 A0 regs0 mem0 md0.
Hypothesis RD0 : rd_cells B mem0.
Hypothesis HTP : ms_tp B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_TP.
Hypothesis HERR : errno_addr B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO.
Hypothesis HGG : ms_got_guard B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GOT_GUARD.
Hypothesis HGD : ms_guard B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GUARD.
Hypothesis HSP47 : spZ regs0 <= 2 ^ 47.
Hypothesis HGLOB : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs0 - CNO_K.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F) (data : Z) (x : list byte).
Hypothesis LED0 : ledger B L0 A0 mem0 Lam peak cnt (2 ^ 64 - 1).
Hypothesis CNT0 : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis XLEN : Z.of_nat (length x) <= 0x300000.
Hypothesis XB : Mem.bytes_at (ms_segs B) mem0 data x.
Hypothesis XBLK : x <> [] -> exists a k, In (a, k) (blocks L0 A0) /\ a <= data /\ data + Z.of_nat (length x) <= a + k.
Hypothesis ROOM : cno_room F b (Z.of_nat (length x)) (cno_tr x) (cno_ok x).
Hypothesis GR0 : Mem.bytes_at (ms_segs B) mem0 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Hypothesis GO0 : Mem.bytes_at (ms_segs B) mem0 GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).

Let J := cj B API L0 A0 regs0 mem0 md0.
Let Q := cno_Q B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x.

Local Abbreviation nx := (Z.of_nat (length x)).
Local Abbreviation ct3 := (cnt + 3 * Z.of_nat (ncalls jr_strtod (zb x))).

(* The callee-saved registers phase C keeps: sp, gp, tp, s0 = one, s1 = two, s2 = nul, s3 = 0 (ran_out), s8..s11. *)
Definition cnoC_R (regs : bvmap 5 word) (one two nul : Z) : Prop :=
  spZ regs = spZ regs0 - 240 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 3 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8 = Z_to_bv 64 one /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 two /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18 = Z_to_bv 64 nul /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19 = Z_to_bv 64 0 /\
  (forall r, 24 <= r <= 27 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 (Z_to_bv 5 r)).

Lemma cnoC_R_rp : forall regs regs' one two nul, cnoC_R regs one two nul -> regs_preserved regs regs' ->
  cnoC_R regs' one two nul.
Proof.
  intros regs regs' one two nul (Hs & H3 & H4 & H8 & H9 & H18 & H19 & H22) RP.
  split; [unfold spZ in *; rewrite <- Hs; f_equal; apply (RP 2); unfold callee_saved; lia|].
  split; [rewrite <- H3; apply (RP 3); unfold callee_saved; lia|].
  split; [rewrite <- H4; apply (RP 4); unfold callee_saved; lia|].
  split; [rewrite <- H8; apply (RP 8); unfold callee_saved; lia|].
  split; [rewrite <- H9; apply (RP 9); unfold callee_saved; lia|].
  split; [rewrite <- H18; apply (RP 18); unfold callee_saved; lia|].
  split; [rewrite <- H19; apply (RP 19); unfold callee_saved; lia|].
  intros r Hr. rewrite <- (H22 r Hr). apply RP. unfold callee_saved. lia.
Qed.

Lemma cnoC_pres : forall regsF, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regsF 2 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 2 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regsF 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 3 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regsF 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regsF 8 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 8 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regsF 9 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 9 ->
  (forall r, 18 <= r <= 27 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regsF (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 (Z_to_bv 5 r)) -> regs_preserved regs0 regsF.
Proof.
  intros regsF H2 H3 H4 H8 H9 H18 r Hr. unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [exact H2 | exact H3 | exact H4 | exact H8 | exact H9 | apply H18; lia].
Qed.

Lemma cnoC_saved_len : length (cno_saved regs0) = 72%nat.
Proof. unfold cno_saved. rewrite !length_app, !Mem.length_le8. reflexivity. Qed.

Lemma cnoC_data : forall L A m md, J L A m md -> Mem.bytes_at (ms_segs B) m data x.
Proof.
  intros L A m md HJ. pose proof XB as XB'. rewrite HS in XB' |- *.
  pose proof XB' as (XB0 & XB1 & _).
  assert (Hx : x = [] \/ x <> []) by (destruct x; [left; reflexivity | right; discriminate]).
  destruct Hx as [Hx|Hx].
  - rewrite Hx. apply bytes_at_nil. lia.
  - apply (cno_bytes_frame B HS mem0 m data x XB'). intros i Hi.
    destruct (XBLK Hx) as (a & k & Hin & Ha & Hk).
    replace (data + i) with (a + (data + i - a)) by lia.
    apply (cj_mem0 B API AX HG L0 A0 regs0 mem0 md0 PRE0 L A m md a k (data + i - a) HJ Hin). lia.
Qed.

Lemma cnoC_aw_cp : forall K L A regs m md E L' A' regs' m' md' live pk ct fl,
  aa_MR API L A m md -> call_post_k B MR K L A regs m md E L' A' regs' m' md' ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling + K <= spZ regs -> (forall a, alloc_statics a -> ~ E a) ->
  alloc_words B m live pk ct fl -> alloc_words B m' live pk ct fl.
Proof.
  intros K L A regs m md E L' A' regs' m' md' live pk ct fl HM CP HK HE (W1 & W2 & W3 & W4).
  assert (EQ : forall a, alloc_statics a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha.
    exact (kb_post_globals B API omx_G K L A regs m md E L' A' regs' m' md' a HG HM CP HK (cno_statics_img a Ha) (HE a Ha)). }
  unfold alloc_words.
  split; [|split; [|split]]; (eapply word_mem_frame; [eassumption|]); intros k Hk; apply EQ; unfold alloc_statics; lia.
Qed.

Lemma cnoC_free : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md bnd p live pk ct fl (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 240 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) ->
  In (p, nx + 16) (user_blocks A) -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
  (forall q k, In (q, k) (user_blocks A0) -> q <> p) -> st_init_done A = true -> rf_ok F A bnd ->
  alloc_words B m live pk ct fl -> bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) ->
  (forall L' A' regs' m' md', J L' A' m' md' -> regs_preserved regs regs' ->
     (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) ->
     st_init_done A' = true -> rf_ok F A' (rf_free F bnd (nx + 16)) -> alloc_words B m' live pk ct fl ->
     bytes_at rsegs m' (spZ regs0 - 72) (cno_saved regs0) ->
     SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) m' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs (Z_to_bv 64 0x18250) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md bnd p live pk ct fl P HJ Hsp Htp Hra Hp R10 HNS HI RF AW BY K.
  pose proof HJ as (HM & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & _). pose proof cno_k_le as HKv.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hcv.
  pose proof (cno_ub_blocks L A p (nx + 16) Hp) as HpB.
  apply (cno_call_free B API HFREE AX F FREE L0 A0 regs0 mem0 md0 PRE0 fx L A regs m md bnd p (nx + 16) P
    HJ Hsp Htp Hra Hp R10 HNS HI RF).
  intros L' A' regs' m' md' HJ' CP SURV HI' RF'.
  pose proof (proj1 (call_post_k_alloc B MR L A regs m md _ L' A' regs' m' md') CP) as CPk.
  pose proof CPk as (_ & _ & _ & _ & PTR & RP & _).
  apply (K L' A' regs' m' md' HJ' RP); [| exact HI' | exact RF' | |].
  - intros q k Hq Hne. pose proof (SURV q k Hq Hne) as Hq'. split; [exact Hq' | exact (PTR q k Hq Hq')].
  - apply (cnoC_aw_cp ALLOC_STACK L A regs m md _ L' A' regs' m' md' live pk ct fl HM CPk);
      [unfold ALLOC_STACK; lia | | exact AW].
    intros a Ha HE. destruct (cno_statics_free B API HG a Ha) as (Hi & _).
    destruct (cno_block_facts B API AX L A m md (ptr_addr L p) (nx + 16) (a - ptr_addr L p) HM HpB ltac:(lia))
      as (_ & _ & _ & _ & Hn).
    replace (ptr_addr L p + (a - ptr_addr L p)) with a in Hn by lia. exact (Hn Hi).
  - apply (cno_hi_cp B API HS L A regs m md ALLOC_STACK _ L' A' regs' m' md' _ _ CPk HM BY); [lia|].
    rewrite cnoC_saved_len. intros i Hi. split.
    + unfold scratch_k, ALLOC_STACK. rewrite HERR. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO. lia.
    + intros HE.
      destruct (cno_block_facts B API AX L A m md (ptr_addr L p) (nx + 16) 0 HM HpB ltac:(lia)) as (_ & _ & Hb & _).
      lia.
Qed.

(* The epilogue (0x13a00): a0 = s3 = 0, the nine saved words back, sp += 240, ret; the post of the contract, with
   g_ran_out and g_own_ran_out still at their entry bytes 0 (cj_gro, cj_own). *)
Lemma cnoC_ep : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md pk bM one two nul,
  J L A m md -> cnoC_R regs one two nul ->
  bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) ->
  frm_zero (@fp_csr fx) ->
  alloc_words B m (lsum Lam) pk ct3 (2 ^ 64 - 1) -> lsum Lam <= pk < 2 ^ 64 -> 0 <= ct3 < 2 ^ 64 -> peak <= pk ->
  st_init_done A = true ->
  (exists E1 E2 E3, cno_dl (cno_tr x) E1 /\ cno_dl (cno_tr x) E2 /\ cno_dl (cno_tr x) E3 /\
     bM = cno_mid F b nx (cno_tr x) (cno_ok x) E1 E2 E3) ->
  rf_ok F A (cno_free3 F bM nx) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs (Z_to_bv 64 0x13a00) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) Q.
Proof.
  intros fx L A regs m md pk bM one two nul HJ (Hsp & G3 & G4 & _ & _ & _ & G19 & G22) BY FZ AW HPK HCT HPP HI
    (E1 & E2 & E3 & DL1 & DL2 & DL3 & EM) RF.
  pose proof HJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRA).
  destruct (kb_md B API L A m md HM) as (Hh & Hz).
  pose proof PRE0 as (_ & _ & _ & Hra0 & _ & HK & HK63 & _). pose proof cno_k_le as HKv.
  assert (E2s : Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 240) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 2).
  { change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) with (spZ regs). rewrite Hsp.
    replace (spZ regs0 - 240 + 240) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
  eapply (cno_jump B HS fx regs _ m md _ _ Q Hh Hz).
  { unfold rmk.
    apply (cno_epilogue (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 5)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 6) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 7) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 11) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 12) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 13) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 14) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 15)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 16) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 17) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 28) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 29) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 30)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 31) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 18)
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 20) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 23)).
    - change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) with (spZ regs). lia.
    - change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) with (spZ regs). rewrite Hsp.
      replace (spZ regs0 - 240 + 168) with (spZ regs0 - 72) by lia. exact BY. }
  intros regs' HGr.
  rewrite (kb_ret_pc _ Hra0).
  apply SR_ret. unfold Q, cno_Q.
  assert (RP : regs_preserved regs0 regs').
  { apply cnoC_pres.
    - rewrite HGr, <- E2s. reflexivity.
    - rewrite HGr, <- G3. reflexivity.
    - rewrite HGr, <- G4. reflexivity.
    - rewrite HGr. reflexivity.
    - rewrite HGr. reflexivity.
    - intros r Hr. rewrite HGr.
      assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ 24 <= r <= 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->|[->|Hr']]]]]]; [reflexivity .. |].
      rewrite <- (G22 r Hr').
      assert (Hr'' : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr'' as [->|[->|[->| ->]]]; reflexivity. }
  assert (A0z : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 10 = Z_to_bv 64 0) by (rewrite HGr, <- G19; reflexivity).
  pose proof (cj_gro B API HG L0 A0 regs0 mem0 md0 PRE0 L A m md HJ GR0) as GRO.
  pose proof (cj_own B API HG L0 A0 regs0 mem0 md0 PRE0 L A m md HJ GO0) as OWN.
  exists fx, L, A, regs', m, md, pk, E1, E2, E3.
  split; [reflexivity|]. split; [exact FZ|].
  split; [exact (cj_final B API L0 A0 regs0 mem0 md0 L A m md regs' HJ RP)|].
  split; [exact (cno_rd_cells B API AX L A m md HM HRA)|].
  split; [exact HI|].
  split; [exact (cno_ledger_cj B API AX HG L0 A0 regs0 mem0 md0 PRE0 L A m md Lam peak cnt (2 ^ 64 - 1) pk ct3
                   (2 ^ 64 - 1) LED0 HJ AW HPK HCT ltac:(lia))|].
  split; [exact HPP|].
  split; [exact (cnoC_data L A m md HJ)|].
  split; [exact GRO|].
  split; [exact DL1|]. split; [exact DL2|]. split; [exact DL3|].
  split; [rewrite <- EM; exact RF|].
  split; [exact A0z|]. split; [exact GRO | exact OWN].
Qed.

Lemma cnoC_nodup_app : forall (l1 l2 : list Z) z, List.NoDup (l1 ++ l2) -> In z l1 -> In z l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 z H H1 H2; [destruct H1|]. cbn [app] in H.
  inversion H as [|? ? Hn H']; subst. destruct H1 as [<-|H1].
  - apply Hn. apply in_or_app. right. exact H2.
  - exact (IH l2 z H' H1 H2).
Qed.

(* A tree on the frame survives a pj_free call on another frame node. *)
Lemma cnoC_keep : forall (d : nat) L A regs m md Lam1 Lam2 pk ct fl L' A' regs' m' md' v Dv p t D,
  J L A m md -> spZ regs = spZ regs0 - 240 ->
  rpost B API (PJ_FREE_K d) L A regs m md (pj_free_writes v Dv) (freed Dv) L' A' regs' m' md' ->
  ledger B L A m Lam1 pk ct fl -> Permutation Lam1 (Dv ++ Lam2) ->
  pj_node (ms_segs B) m (lin Lam1) p t D -> (forall a k, In (a, k) D -> In (a, k) Lam2) ->
  spZ regs0 - 240 <= p -> p + 56 <= spZ regs0 -> spZ regs0 - 240 <= v -> (p + 56 <= v \/ v + 56 <= p) ->
  pj_node (ms_segs B) m' (lin Lam2) p t D.
Proof.
  intros d L A regs m md Lam1 Lam2 pk ct fl L' A' regs' m' md' v Dv p t D HJ Hsp RP LG HP N HD H1 H2 Hv0 H3.
  pose proof HJ as (HM & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _). pose proof cno_k_le as HKv.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hcv.
  pose proof LG as (_ & _ & _ & _ & ND & FA). rewrite Forall_forall in FA.
  apply (proj1 (NoDup_ListNoDup _)) in ND.
  assert (ND2 : List.NoDup (map fst Dv ++ map fst Lam2)).
  { rewrite <- map_app. exact (Permutation_NoDup (Permutation_map fst HP) ND). }
  assert (LBV : forall a k, In (a, k) Dv -> lblock B L A m a k).
  { intros a k H. apply (FA (a, k)). apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact H. }
  assert (LB2 : forall a k, In (a, k) Lam2 -> lblock B L A m a k).
  { intros a k H. apply (FA (a, k)). apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact H. }
  apply (cno_tree_rpost B API HS L A regs m md _ _ _ L' A' regs' m' md' Lam1 Lam2 pk ct fl p t D RP LG N HD);
    [lia | lia | |].
  - intros i Hi. split.
    + unfold scratch_k. rewrite HERR. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO. lia.
    + unfold pj_free_writes, blk_set. intros (_ & [Hv | [(a & k & Hin & Hai) | Hst]]).
      * lia.
      * destruct (LBV a k Hin) as (Hk & HinB & _ & _).
        destruct (cno_block_range B API L A m md _ _ HM HinB) as [Hb1 Hb2]. lia.
      * destruct (cno_statics_free B API HG _ Hst) as (_ & Hlt & _). lia.
  - intros a k Hin. destruct (LB2 a k (HD a k Hin)) as (Hk & HinB & _ & HNI).
    destruct (cno_block_range B API L A m md _ _ HM HinB) as [Hb1 Hb2]. split.
    + unfold freed. replace (a - 16 + 16) with a by lia. replace (k + 16 - 16) with k by lia.
      intros Hf. exact (cnoC_nodup_app _ _ a ND2 (in_map fst _ _ Hf) (in_map fst _ _ (HD a k Hin))).
    + intros i Hi. unfold pj_free_writes, blk_set. intros (_ & [Hv | [(a' & k' & Hin' & Hai) | Hst]]).
      * lia.
      * destruct (LBV a' k' Hin') as (Hk' & HinB' & _ & _).
        assert (Hne : (a - 16, k + 16) <> (a' - 16, k' + 16)).
        { intros E. injection E as E1 E2. assert (Ea : a' = a) by lia. rewrite Ea in Hin'.
          exact (cnoC_nodup_app _ _ a ND2 (in_map fst _ _ Hin') (in_map fst _ _ (HD a k Hin))). }
        destruct (cno_blocks_sep B API L A m md _ _ HM HinB HinB' Hne) as [S|S]; cbn [fst snd] in S; lia.
      * destruct (cno_statics_free B API HG _ Hst) as (Himg & _). apply (HNI (i + 16)); [lia|].
        replace (a - 16 + (i + 16)) with (a + i) by lia. exact Himg.
Qed.

(* The saved registers' bytes survive a pj_free call on a frame node below them. *)
Lemma cnoC_saved_keep : forall (d : nat) L A regs m md L' A' regs' m' md' v Dv,
  J L A m md -> spZ regs = spZ regs0 - 240 ->
  rpost B API (PJ_FREE_K d) L A regs m md (pj_free_writes v Dv) (freed Dv) L' A' regs' m' md' ->
  (forall a k, In (a, k) Dv -> In (a - 16, k + 16) (blocks L A)) ->
  v + 56 <= spZ regs0 - 72 ->
  bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) -> bytes_at rsegs m' (spZ regs0 - 72) (cno_saved regs0).
Proof.
  intros d L A regs m md L' A' regs' m' md' v Dv HJ Hsp RP HDB Hv BY.
  pose proof HJ as (HM & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _). pose proof cno_k_le as HKv.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hcv.
  apply (cno_hi_rpost B API HS L A regs m md _ _ _ L' A' regs' m' md' _ _ RP BY); [lia|].
  rewrite cnoC_saved_len. intros i Hi. split.
  - unfold scratch_k. rewrite HERR. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO. lia.
  - unfold pj_free_writes, blk_set. intros (_ & [Hv' | [(a & k & Hin & Hai) | Hst]]).
    + lia.
    + destruct (cno_block_range B API L A m md _ _ HM (HDB a k Hin)) as [Hb1 Hb2]. lia.
    + destruct (cno_statics_free B API HG _ Hst) as (_ & Hlt & _). lia.
Qed.

(* The three copy blocks survive a pj_free call (its freed blocks are tree blocks, not copies). *)
Lemma cnoC_blk_keep : forall (d : nat) L A regs m md E L' A' regs' m' md' Dv q c,
  rpost B API (PJ_FREE_K d) L A regs m md E (freed Dv) L' A' regs' m' md' ->
  In (q, nx + 16) (user_blocks A) -> ptr_addr L q = c ->
  (forall a k, In (a, k) Dv -> (a - 16, k + 16) <> (c, nx + 16)) ->
  In (q, nx + 16) (user_blocks A') /\ ptr_addr L' q = c.
Proof.
  intros d L A regs m md E L' A' regs' m' md' Dv q c RP Hq Hc HDv.
  pose proof RP as (_ & _ & _ & _ & _ & _ & _ & SUR & PTR & _).
  assert (Hq' : In (q, nx + 16) (user_blocks A')).
  { apply (SUR q (nx + 16) Hq). unfold freed. intros Hf. apply (HDv _ _ Hf). rewrite Hc.
    f_equal; lia. }
  split; [exact Hq'|]. rewrite (PTR q (nx + 16) Hq Hq'). exact Hc.
Qed.

Lemma cnoC_R_mv : forall regs regs' one two nul, cnoC_R regs one two nul ->
  (forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ 24 <= r <= 27 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs (Z_to_bv 5 r)) ->
  cnoC_R regs' one two nul.
Proof.
  intros regs regs' one two nul (Hs & H3 & H4 & H8 & H9 & H18 & H19 & H22) E.
  split; [unfold spZ in *; rewrite <- Hs; f_equal; apply (E 2); lia|].
  split; [rewrite <- H3; apply (E 3); lia|].
  split; [rewrite <- H4; apply (E 4); lia|].
  split; [rewrite <- H8; apply (E 8); lia|].
  split; [rewrite <- H9; apply (E 9); lia|].
  split; [rewrite <- H18; apply (E 18); lia|].
  split; [rewrite <- H19; apply (E 19); lia|].
  intros r Hr. rewrite <- (H22 r Hr). apply E. lia.
Qed.

Ltac cnoC_mvE HG :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
  intros r Hr; rewrite HG;
  destruct Hr as [->|[->|[->|[->|[->|[->|[->|Hr]]]]]]]; [reflexivity .. |];
  assert (Hr' : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->| ->]]]; reflexivity.

(* One tree-free call (0x16340) with the frame facts carried. *)
Lemma cnoC_pjf : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md Lamc pk bnd v Dv u one two nul (P : config -> Prop),
  J L A m md -> cnoC_R regs one two nul -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) -> frm_zero (@fp_csr fx) ->
  ledger B L A m Lamc pk ct3 (2 ^ 64 - 1) -> rf_ok F A bnd ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 v -> spZ regs0 - 240 <= v -> v + 56 <= spZ regs0 - 72 -> v mod 8 = 0 ->
  st_init_done A = true -> pj_node (ms_segs B) m (lin Lamc) v u Dv -> (depth u <= 32)%nat ->
  (forall a k, In (a, k) Dv -> ~ In (a - 16, k + 16) (blocks L0 A0)) ->
  bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) ->
  (forall L' A' regs' m' md' Lam',
     J L' A' m' md' -> cnoC_R regs' one two nul ->
     rpost B API (PJ_FREE_K (depth u)) L A regs m md (pj_free_writes v Dv) (freed Dv) L' A' regs' m' md' ->
     Permutation Lamc (Dv ++ Lam') -> ledger B L' A' m' Lam' pk ct3 (2 ^ 64 - 1) ->
     (exists D', Permutation Dv D' /\ rf_ok F A' (rf_frees F bnd D')) ->
     bytes_at rsegs m' (spZ regs0 - 72) (cno_saved regs0) -> st_init_done A' = true ->
     SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) m' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs (Z_to_bv 64 0x16340) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md Lamc pk bnd v Dv u one two nul P HJ R Hra FZ LG RF G10 Hv1 Hv2 Hv8 HI N HDEP HNW BY K.
  pose proof R as (Hsp & _ & G4 & _).
  pose proof LG as (_ & _ & _ & _ & _ & FA). rewrite Forall_forall in FA.
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _). pose proof cno_k_le as HKv.
  pose proof (cno_free_k (depth u) HDEP) as HFK.
  apply (cno_call_pjfree B API HS AX HG F PJFREE L0 A0 regs0 mem0 md0 PRE0 HTP HERR HGG HGD HSP47 HGLOB fx L A regs m md
           Lamc pk ct3 bnd v u Dv P HJ Hsp G4 Hra FZ LG RF G10 Hv1 ltac:(lia) Hv8 HI N HDEP HNW).
  intros L' A' regs' m' md' Lam' HJ' RP HP LG' HRF Z'.
  pose proof RP as (_ & _ & _ & _ & HI' & _ & _ & _ & _ & RPr & _).
  assert (DB : forall a k, In (a, k) Dv -> lblock B L A m a k)
    by (intros a k Hin; exact (FA (a, k) (Permutation_in _ (Permutation_sym HP) (in_or_app _ _ _ (or_introl Hin))))).
  apply (K L' A' regs' m' md' Lam' HJ' (cnoC_R_rp regs regs' one two nul R RPr) RP HP LG' HRF); [| exact (HI' HI)].
  apply (cnoC_saved_keep (depth u) L A regs m md L' A' regs' m' md' v Dv HJ Hsp RP); [| exact Hv2 | exact BY].
  intros a k Hin. exact (proj1 (proj2 (DB a k Hin))).
Qed.

Lemma cnoC_holds : cno_KC B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x.
Proof.
  unfold cno_KC.
  intros fx L A regs m md Lam3 pk q1 q2 q3 one two nul u D1 D2 D0 bC HJ Hsp Hra G3 G4 G8 G9 G18 G19 G22 G10 BY _ FZ
    LED HPK HP3 N1 N2 N0 HDEP HNEW Q1 P1 Q2 P2 Q3 P3 HQ0 N12 N13 N23 HI RF BR.
  pose proof PRE0 as (_ & _ & _ & Hra0 & HS16 & HK & HK63 & _). pose proof cno_k_le as HKv.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hcv.
  assert (M8 : forall o, o mod 8 = 0 -> (spZ regs0 - 240 + o) mod 8 = 0)
    by (intros o Ho; clear - HS16 Ho; Z.div_mod_to_equations; lia).
  assert (M0 : (spZ regs0 - 240) mod 8 = 0) by (clear - HS16; Z.div_mod_to_equations; lia).
  assert (R0 : cnoC_R regs one two nul) by (split; [exact Hsp|]; repeat split; assumption).
  assert (HPa : Permutation (D0 ++ D2 ++ D1 ++ Lam) (D1 ++ D2 ++ D0 ++ Lam)).
  { rewrite (app_assoc D0 D2 (D1 ++ Lam)).
    apply (Permutation_trans (Permutation_app_swap_app (D0 ++ D2) D1 Lam)).
    apply Permutation_app_head. rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  assert (NW1 : forall a k, In (a, k) D1 -> ~ In (a - 16, k + 16) (blocks L0 A0) /\ (a - 16, k + 16) <> (one, nx + 16) /\
                (a - 16, k + 16) <> (two, nx + 16) /\ (a - 16, k + 16) <> (nul, nx + 16))
    by (intros a k H; apply HNEW; apply in_or_app; left; exact H).
  assert (NW2 : forall a k, In (a, k) D2 -> ~ In (a - 16, k + 16) (blocks L0 A0) /\ (a - 16, k + 16) <> (one, nx + 16) /\
                (a - 16, k + 16) <> (two, nx + 16) /\ (a - 16, k + 16) <> (nul, nx + 16))
    by (intros a k H; apply HNEW; apply in_or_app; right; apply in_or_app; left; exact H).
  assert (NW0 : forall a k, In (a, k) D0 -> ~ In (a - 16, k + 16) (blocks L0 A0) /\ (a - 16, k + 16) <> (one, nx + 16) /\
                (a - 16, k + 16) <> (two, nx + 16) /\ (a - 16, k + 16) <> (nul, nx + 16))
    by (intros a k H; apply HNEW; apply in_or_app; right; apply in_or_app; right; exact H).
  (* first tree free: sp + 0x70, D1 *)
  apply (cnoC_pjf fx L A regs m md Lam3 pk bC (spZ regs0 - 240 + 112) D1 u one two nul Q HJ R0);
    [rewrite Hra; cnoC_ret | exact FZ | exact LED | exact RF | exact G10 | lia | lia | apply M8; reflexivity | exact HI
    | exact N1 | exact HDEP | intros a k H; exact (proj1 (NW1 a k H)) | exact BY |].
  intros L1 A1 regs1 m1 md1 Lam4 HJ1 R1 RP1 HP4 LED1 (D1' & PD1 & RF1) BY1 HI1.
  rewrite Hra.
  assert (P4 : Permutation Lam4 (D2 ++ D0 ++ Lam)).
  { apply (Permutation_app_inv_l D1). apply (Permutation_trans (Permutation_sym HP4)). exact (Permutation_trans HP3 HPa). }
  assert (N2a : pj_node (ms_segs B) m1 (lin Lam4) (spZ regs0 - 240 + 56) u D2).
  { apply (cnoC_keep (depth u) L A regs m md Lam3 Lam4 pk ct3 (2 ^ 64 - 1) L1 A1 regs1 m1 md1 (spZ regs0 - 240 + 112) D1
             (spZ regs0 - 240 + 56) u D2 HJ Hsp RP1 LED HP4 N2); [|lia|lia|lia|lia].
    intros a k H. apply (Permutation_in _ (Permutation_sym P4)). apply in_or_app. left. exact H. }
  assert (N0a : pj_node (ms_segs B) m1 (lin Lam4) (spZ regs0 - 240) u D0).
  { apply (cnoC_keep (depth u) L A regs m md Lam3 Lam4 pk ct3 (2 ^ 64 - 1) L1 A1 regs1 m1 md1 (spZ regs0 - 240 + 112) D1
             (spZ regs0 - 240) u D0 HJ Hsp RP1 LED HP4 N0); [|lia|lia|lia|lia].
    intros a k H. apply (Permutation_in _ (Permutation_sym P4)). apply in_or_app. right. apply in_or_app. left. exact H. }
  destruct (cnoC_blk_keep (depth u) L A regs m md _ L1 A1 regs1 m1 md1 D1 q1 one RP1 Q1 P1
              (fun a k H => proj1 (proj2 (NW1 a k H)))) as [Q1a P1a].
  destruct (cnoC_blk_keep (depth u) L A regs m md _ L1 A1 regs1 m1 md1 D1 q2 two RP1 Q2 P2
              (fun a k H => proj1 (proj2 (proj2 (NW1 a k H))))) as [Q2a P2a].
  destruct (cnoC_blk_keep (depth u) L A regs m md _ L1 A1 regs1 m1 md1 D1 q3 nul RP1 Q3 P3
              (fun a k H => proj2 (proj2 (proj2 (NW1 a k H))))) as [Q3a P3a].
  (* 0x139d8: jump to the second tree free *)
  pose proof HJ1 as (HM1 & _). destruct (kb_md B API L1 A1 m1 md1 HM1) as (Hh1 & Hz1).
  pose proof R1 as (Hsp1 & _).
  eapply (cno_jump B HS fx regs1 _ m1 md1 _ _ Q Hh1 Hz1).
  { unfold rmk. apply cno_mv_free2. change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 2)) with (spZ regs1). lia. }
  intros regs2 HG2.
  assert (R2 : cnoC_R regs2 one two nul) by (apply (cnoC_R_mv regs1 regs2 one two nul R1); cnoC_mvE HG2).
  assert (G10b : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 10 = Z_to_bv 64 (spZ regs0 - 240 + 56)).
  { transitivity (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 2) + 56)); [rewrite HG2; reflexivity|].
    change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 2)) with (spZ regs1). rewrite Hsp1. reflexivity. }
  assert (RA2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 1 = Z_to_bv 64 0x139e0) by (rewrite HG2; reflexivity).
  (* second tree free: sp + 0x38, D2 *)
  apply (cnoC_pjf fx L1 A1 regs2 m1 md1 Lam4 pk (rf_frees F bC D1') (spZ regs0 - 240 + 56) D2 u one two nul Q HJ1 R2);
    [rewrite RA2; cnoC_ret | exact FZ | exact LED1 | exact RF1 | exact G10b | lia | lia | apply M8; reflexivity
    | exact HI1 | exact N2a | exact HDEP | intros a k H; exact (proj1 (NW2 a k H)) | exact BY1 |].
  intros L2 A2 regs3 m2 md2 Lam5 HJ2 R3 RP2 HP5 LED2 (D2' & PD2 & RF2) BY2 HI2.
  rewrite RA2.
  assert (P5 : Permutation Lam5 (D0 ++ Lam)).
  { apply (Permutation_app_inv_l D2). apply (Permutation_trans (Permutation_sym HP5)). exact P4. }
  pose proof R2 as (Hsp2 & _).
  assert (N0b : pj_node (ms_segs B) m2 (lin Lam5) (spZ regs0 - 240) u D0).
  { apply (cnoC_keep (depth u) L1 A1 regs2 m1 md1 Lam4 Lam5 pk ct3 (2 ^ 64 - 1) L2 A2 regs3 m2 md2 (spZ regs0 - 240 + 56) D2
             (spZ regs0 - 240) u D0 HJ1 Hsp2 RP2 LED1 HP5 N0a); [|lia|lia|lia|lia].
    intros a k H. apply (Permutation_in _ (Permutation_sym P5)). apply in_or_app. left. exact H. }
  destruct (cnoC_blk_keep (depth u) L1 A1 regs2 m1 md1 _ L2 A2 regs3 m2 md2 D2 q1 one RP2 Q1a P1a
              (fun a k H => proj1 (proj2 (NW2 a k H)))) as [Q1b P1b].
  destruct (cnoC_blk_keep (depth u) L1 A1 regs2 m1 md1 _ L2 A2 regs3 m2 md2 D2 q2 two RP2 Q2a P2a
              (fun a k H => proj1 (proj2 (proj2 (NW2 a k H))))) as [Q2b P2b].
  destruct (cnoC_blk_keep (depth u) L1 A1 regs2 m1 md1 _ L2 A2 regs3 m2 md2 D2 q3 nul RP2 Q3a P3a
              (fun a k H => proj2 (proj2 (proj2 (NW2 a k H))))) as [Q3b P3b].
  (* 0x139e0: jump to the third tree free *)
  pose proof HJ2 as (HM2 & _). destruct (kb_md B API L2 A2 m2 md2 HM2) as (Hh2 & Hz2).
  pose proof R3 as (Hsp3 & _).
  eapply (cno_jump B HS fx regs3 _ m2 md2 _ _ Q Hh2 Hz2).
  { unfold rmk. apply cno_mv_free3. }
  intros regs4 HG4.
  assert (R4 : cnoC_R regs4 one two nul) by (apply (cnoC_R_mv regs3 regs4 one two nul R3); cnoC_mvE HG4).
  assert (G10c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 10 = Z_to_bv 64 (spZ regs0 - 240)).
  { transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 2); [rewrite HG4; reflexivity|].
    rewrite <- Hsp3. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (RA4 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 1 = Z_to_bv 64 0x139e8) by (rewrite HG4; reflexivity).
  (* third tree free: sp, D0 *)
  apply (cnoC_pjf fx L2 A2 regs4 m2 md2 Lam5 pk (rf_frees F (rf_frees F bC D1') D2') (spZ regs0 - 240) D0 u one two nul Q
           HJ2 R4);
    [rewrite RA4; cnoC_ret | exact FZ | exact LED2 | exact RF2 | exact G10c | lia | lia | exact M0
    | exact HI2 | exact N0b | exact HDEP | intros a k H; exact (proj1 (NW0 a k H)) | exact BY2 |].
  intros L3 A3 regs5 m3 md3 Lam6 HJ3 R5 RP3 HP6 LED3 (D0' & PD0 & RF3) BY3 HI3.
  rewrite RA4.
  assert (P6 : Permutation Lam6 Lam).
  { apply (Permutation_app_inv_l D0). apply (Permutation_trans (Permutation_sym HP6)). exact P5. }
  destruct (cnoC_blk_keep (depth u) L2 A2 regs4 m2 md2 _ L3 A3 regs5 m3 md3 D0 q1 one RP3 Q1b P1b
              (fun a k H => proj1 (proj2 (NW0 a k H)))) as [Q1c P1c].
  destruct (cnoC_blk_keep (depth u) L2 A2 regs4 m2 md2 _ L3 A3 regs5 m3 md3 D0 q2 two RP3 Q2b P2b
              (fun a k H => proj1 (proj2 (proj2 (NW0 a k H))))) as [Q2c P2c].
  destruct (cnoC_blk_keep (depth u) L2 A2 regs4 m2 md2 _ L3 A3 regs5 m3 md3 D0 q3 nul RP3 Q3b P3b
              (fun a k H => proj2 (proj2 (proj2 (NW0 a k H))))) as [Q3c P3c].
  pose proof LED3 as (AW3 & HPK3 & HCT3 & _).
  rewrite (cno_lsum_perm Lam6 Lam P6) in AW3, HPK3.
  set (bM := rf_frees F (rf_frees F (rf_frees F bC D1') D2') D0').
  (* 0x139e8: first block free, s0 = one *)
  pose proof HJ3 as (HM3 & _). destruct (kb_md B API L3 A3 m3 md3 HM3) as (Hh3 & Hz3).
  pose proof R5 as (Hsp5 & _ & G45 & G85 & _).
  eapply (cno_jump B HS fx regs5 _ m3 md3 _ _ Q Hh3 Hz3).
  { unfold rmk. apply cno_mv_rel1. }
  intros regs6 HG6.
  assert (R6 : cnoC_R regs6 one two nul) by (apply (cnoC_R_mv regs5 regs6 one two nul R5); cnoC_mvE HG6).
  pose proof R6 as (Hsp6 & _ & G46 & _).
  assert (RA6 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs6 1 = Z_to_bv 64 0x139f0) by (rewrite HG6; reflexivity).
  apply (cnoC_free fx L3 A3 regs6 m3 md3 bM q1 (lsum Lam) pk ct3 (2 ^ 64 - 1) Q HJ3 Hsp6 G46);
    [rewrite RA6; cnoC_ret | exact Q1c | | intros q k H; exact (proj1 (HQ0 q k H)) | exact HI3 | exact RF3 | exact AW3
    | exact BY3 |].
  { rewrite P1c. transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs5 8); [rewrite HG6; reflexivity | exact G85]. }
  intros L4 A4 regs7 m4 md4 HJ4 RP4 SUR4 HI4 RF4 AW4 BY4.
  rewrite RA6.
  destruct (SUR4 q2 _ Q2c (fun E => N12 (eq_sym E))) as [Q2d P2d]. rewrite P2c in P2d.
  destruct (SUR4 q3 _ Q3c (fun E => N13 (eq_sym E))) as [Q3d P3d]. rewrite P3c in P3d.
  pose proof (cnoC_R_rp regs6 regs7 one two nul R6 RP4) as R7.
  (* 0x139f0: second block free, s1 = two *)
  pose proof HJ4 as (HM4 & _). destruct (kb_md B API L4 A4 m4 md4 HM4) as (Hh4 & Hz4).
  pose proof R7 as (Hsp7 & _ & G47 & _ & G97 & _).
  eapply (cno_jump B HS fx regs7 _ m4 md4 _ _ Q Hh4 Hz4).
  { unfold rmk. apply cno_mv_rel2. }
  intros regs8 HG8.
  assert (R8 : cnoC_R regs8 one two nul) by (apply (cnoC_R_mv regs7 regs8 one two nul R7); cnoC_mvE HG8).
  pose proof R8 as (Hsp8 & _ & G48 & _).
  assert (RA8 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs8 1 = Z_to_bv 64 0x139f8) by (rewrite HG8; reflexivity).
  apply (cnoC_free fx L4 A4 regs8 m4 md4 (rf_free F bM (nx + 16)) q2 (lsum Lam) pk ct3 (2 ^ 64 - 1) Q HJ4 Hsp8 G48);
    [rewrite RA8; cnoC_ret | exact Q2d | | intros q k H; exact (proj1 (proj2 (HQ0 q k H))) | exact HI4 | exact RF4
    | exact AW4 | exact BY4 |].
  { rewrite P2d. transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs7 9); [rewrite HG8; reflexivity | exact G97]. }
  intros L5 A5 regs9 m5 md5 HJ5 RP5 SUR5 HI5 RF5 AW5 BY5.
  rewrite RA8.
  destruct (SUR5 q3 _ Q3d (fun E => N23 (eq_sym E))) as [Q3e P3e]. rewrite P3d in P3e.
  pose proof (cnoC_R_rp regs8 regs9 one two nul R8 RP5) as R9.
  (* 0x139f8: third block free, s2 = nul *)
  pose proof HJ5 as (HM5 & _). destruct (kb_md B API L5 A5 m5 md5 HM5) as (Hh5 & Hz5).
  pose proof R9 as (Hsp9 & _ & G49 & _ & _ & G189 & _).
  eapply (cno_jump B HS fx regs9 _ m5 md5 _ _ Q Hh5 Hz5).
  { unfold rmk. apply cno_mv_rel3. }
  intros regs10 HG10.
  assert (R10 : cnoC_R regs10 one two nul) by (apply (cnoC_R_mv regs9 regs10 one two nul R9); cnoC_mvE HG10).
  pose proof R10 as (Hsp10 & _ & G410 & _).
  assert (RA10 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs10 1 = Z_to_bv 64 0x13a00) by (rewrite HG10; reflexivity).
  apply (cnoC_free fx L5 A5 regs10 m5 md5 (rf_free F (rf_free F bM (nx + 16)) (nx + 16)) q3 (lsum Lam) pk ct3
           (2 ^ 64 - 1) Q HJ5 Hsp10 G410);
    [rewrite RA10; cnoC_ret | exact Q3e | | intros q k H; exact (proj2 (proj2 (HQ0 q k H))) | exact HI5 | exact RF5
    | exact AW5 | exact BY5 |].
  { rewrite P3e. transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs9 18); [rewrite HG10; reflexivity | exact G189]. }
  intros L6 A6 regs11 m6 md6 HJ6 RP6 SUR6 HI6 RF6 AW6 BY6.
  rewrite RA10.
  (* 0x13a00: a0 = s3, the epilogue *)
  apply (cnoC_ep fx L6 A6 regs11 m6 md6 pk bM one two nul HJ6 (cnoC_R_rp regs10 regs11 one two nul R10 RP6) BY6 FZ
           AW6 HPK3 HCT3 HPK HI6); [| exact RF6].
  destruct (BR D1' D2' D0' PD1 PD2 PD0) as (E1 & E2 & E3 & DL1 & DL2 & DL3 & EQ).
  exists E1, E2, E3. split; [exact DL1|]. split; [exact DL2|]. split; [exact DL3|]. exact EQ.
Qed.

End Ph.
