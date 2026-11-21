(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb1 Z_tr_cb2 Z_tr_cb3 Z_tr_cb4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees TreesTab SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cb_iter_post (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT sx : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 wbb PB' PD' BB' BV' pcx m',
    ms' = MS (ucbR L LT DT (sx + 1 + 1 + 1) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ sbs_run (upd4 s PB PD BB BV) (sym_calls (upd4 s PB PD BB BV) lfc ldl dfc ddl sx) = upd4 s PB' PD' BB' BV'
    /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ byt PB'
    /\ ((pcx = 0x1e040 /\ ds_sym_next s <= sx + 3) \/ (pcx = 0x1da00 /\ sx + 3 < ds_sym_next s)).

Lemma cb_iter : forall (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> ct_readable (Wem L) m DT dfc ddl 30 ->
  0 < LT -> LT + 4 * 286 < 2^63 -> 0 < DT -> DT + 4 * 30 < 2^63 -> LT mod 2 = 0 -> DT mod 2 = 0 ->
  c15 lfc 286 -> c15 dfc 30 ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB -> 0 <= ds_lit_bufsize s -> 0 <= ds_sym_next s -> ds_sym_next s + 3 < 2^31 -> sx < ds_sym_next s ->
  sym_ok 65536 (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ->
  evt usegs (cb_iter_post L s lfc ldl dfc ddl LT DT sx PB PD BB BV ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1da00) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RDL RDD RLT1 RLT2 RDT1 RDT2 ALT ADT RLf RDf RBV RPD BYT Rlb Rsn1 Rsn2 Hsx SOK.
  pose proof SOK as (Hsx0 & _).
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  call (cb_body L s lfc ldl dfc ddl LT DT sx PB PD BB BV wbb).
  1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDL. } 1:{ exact RDD. } 1:{ exact RLT1. } 1:{ exact RLT2. }
  1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact ALT. } 1:{ exact ADT. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact BYT. }
  1:{ exact Rlb. } 1:{ lia. } 1:{ exact SOK. }
  match goal with H : EM _ _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of H with EM mm _ _ _ _ _ _ => pose proof H as EMo end end.
  open_EM EMo. unfold ucbR. zs2. zs2. zstep. reg_as (sx + 3) (sx + 1 + 1 + 1).
  br_cases K.
  - apply evt_done. unfold cb_iter_post, ucbR. do 18 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    left. split; [reflexivity| lia].
  - apply evt_done. unfold cb_iter_post, ucbR. do 18 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    right. split; [reflexivity| lia].
Qed.

(* [comment removed for export] *)
Definition cb_loop_post (L : dlay) (s : deflate_state) (LT DT : Z) (R : deflate_state)
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 sx' wbb PB' PD' BB' BV' m',
    ms' = MS (ucbR L LT DT sx' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1e040) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV' /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ byt PB'.

Lemma cb_loop : forall (f : nat) (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV sx : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 LT lfc ldl 286 -> ct_readable (Wem L) m0 DT dfc ddl 30 ->
  0 < LT -> LT + 4 * 286 < 2^63 -> 0 < DT -> DT + 4 * 30 < 2^63 -> LT mod 2 = 0 -> DT mod 2 = 0 ->
  c15 lfc 286 -> c15 dfc 30 ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB -> 0 <= ds_lit_bufsize s -> 0 <= ds_sym_next s -> ds_sym_next s + 3 < 2^31 ->
  sx < ds_sym_next s -> ds_sym_next s - sx <= 3 * Z.of_nat (S f) ->
  cb_ok 65536 (S f) (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ->
  R = compress_block_loop (S f) (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ->
  evt usegs (cb_loop_post L s LT DT R ra sp gp tp s11 F fc m0)
      (MS (ucbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1da00) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros EMH HBB MI LAY MU WM RDL RDD RLT1 RLT2 RDT1 RDT2 ALT ADT RLf RDf RBV RPD BYT Rlb Rsn1 Rsn2 Hsx SNF CBOK ER.
  - cbn [cb_ok] in CBOK. destruct CBOK as [SOK NEXT]. pose proof SOK as (Hsx0 & _). rewrite cb_loop_S in ER. cbv zeta in ER.
    call (cb_iter L s lfc ldl dfc ddl LT DT sx PB PD BB BV wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| apply sub_fp_refl]. } 1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact ALT. } 1:{ exact ADT. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact BYT. }
    1:{ exact Rlb. } 1:{ exact Rsn1. } 1:{ exact Rsn2. } 1:{ exact Hsx. } 1:{ exact SOK. }
    match goal with E : sbs_run _ _ = _ |- _ => rewrite E in ER; rewrite upd4_sym_next in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    rewrite (proj2 (Z.ltb_ge _ _)) in ER by lia.
    apply evt_done. unfold cb_loop_post, ucbR. do 18 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [exact ER|]. split; [assumption|]. split; assumption.
  - cbn [cb_ok] in CBOK. destruct CBOK as [SOK NEXT]. pose proof SOK as (Hsx0 & _). rewrite cb_loop_S in ER. cbv zeta in ER, NEXT.
    call (cb_iter L s lfc ldl dfc ddl LT DT sx PB PD BB BV wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| apply sub_fp_refl]. } 1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact ALT. } 1:{ exact ADT. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact BYT. }
    1:{ exact Rlb. } 1:{ exact Rsn1. } 1:{ exact Rsn2. } 1:{ exact Hsx. } 1:{ exact SOK. }
    match goal with E : sbs_run _ _ = _ |- _ => rewrite E in ER, NEXT; rewrite upd4_sym_next in ER, NEXT end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
    + rewrite (proj2 (Z.ltb_ge _ _)) in ER by lia.
      apply evt_done. unfold cb_loop_post, ucbR. do 18 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [exact ER|]. split; [assumption|]. split; assumption.
    + rewrite (proj2 (Z.ltb_lt _ _)) in ER, NEXT by lia.
      eapply (IH L s lfc ldl dfc ddl LT DT R m0); try eassumption; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac close_lens_sbF LENS :=
  let l1 := fresh in let l2 := fresh in let l3 := fresh in let l4 := fresh in let l5 := fresh in let l6 := fresh in let l7 := fresh in
  let l8 := fresh in let l9 := fresh in let l10 := fresh in let l11 := fresh in let l12 := fresh in let l13 := fresh in
  destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
  constructor; unfold upd4; dsred; rewrite ?sbF_PB_len in *; first [assumption | rewrite ?sbF_PB_len; assumption].
Ltac cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY :=
  constructor; [exact HA| exact GB| exact GC| exact HD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
               | exact Gwin| exact Gprev| exact Ghead| exact HP| | exact LAY].

Definition Z_COMPRESS_BLOCK : Z := 0x1d954.

Notation cbW L lo sp := [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] (only parsing).

Definition compress_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch (cbW L lo sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DST m' L (compress_block s lfc ldl dfc ddl).

(* [comment removed for export] *)
Lemma compress_block_spec : forall (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> dlay_below L lo (bv_unsigned sp) ->
  ct_readable (cbW L lo sp) m LT lfc ldl 286 -> ct_readable (cbW L lo sp) m DT dfc ddl 30 ->
  0 < LT -> LT + 4 * 286 < 2^63 -> 0 < DT -> DT + 4 * 30 < 2^63 -> LT mod 2 = 0 -> DT mod 2 = 0 ->
  c15 lfc 286 -> c15 dfc 30 ->
  compress_block_ok 65536 s lfc ldl dfc ddl -> 0 <= ds_lit_bufsize s -> 0 <= ds_sym_next s -> ds_sym_next s + 3 < 2^31 ->
  a0 = wz (dl_As L) -> a1 = wz LT -> a2 = wz DT ->
  evt usegs (compress_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s lfc ldl dfc ddl lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_COMPRESS_BLOCK) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST MI STK LO BEL RDL RDD RLT1 RLT2 RDT1 RDT2 ALT ADT RLf RDf (BI & PB0 & CBOK & ENDOK) Rlb Rsn1 Rsn2 -> -> ->. unfold Z_COMPRESS_BLOCK.
  pose proof BI as (RBV & RBB & RPD).
  pose proof (munch_refl (cbW L lo sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
  open_DST ST. lay_open LAY. below_open BEL. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  carve_frame 96%nat STK.
  do 12 zstep.
  mv_group dsA_munch GA MUs WM. mv_group dsD_munch GD MUs WM. mv_group dpend_munch Gpend MUs WM. clear MUs.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH. clear GA GD Gpend.
  assert (HBB : bv_unsigned (wz (ds_bi_buf s)) mod 2^16 = ds_bi_buf s mod 2^16) by apply lo16_unsigned_wz.
  assert (BYT : byt (ds_pending_buf s)) by exact PB0.
  assert (EX0 : upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) = s) by apply upd4_self.
  pose proof EMH as EMo. open_EM EMo.
  ustep CB_TRAP. ustep CB_TRAP. zs2. zs2. zs2. zs2. clear GA GD Gpend LPB LNP0.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    assert (EQF : compress_block s lfc ldl dfc ddl
                  = upd4 s (sbF_PB (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) (arr_get lfc 256) (arr_get ldl 256))
                           (sbF_PD (ds_pending s) (ds_bi_valid s) (arr_get ldl 256)) (sbF_BB (ds_bi_buf s) (ds_bi_valid s) (arr_get lfc 256) (arr_get ldl 256))
                           (sbF_BV (ds_bi_valid s) (arr_get ldl 256))).
    { unfold compress_block. rewrite (proj2 (Z.eqb_eq _ _) K). cbn [negb]. unfold send_code, END_BLOCK. rewrite <- send_bits_sbF, EX0. reflexivity. }
    cbv zeta in ENDOK. rewrite (proj2 (Z.eqb_eq _ _) K) in ENDOK. cbn [negb] in ENDOK. unfold END_BLOCK in ENDOK. rewrite <- EX0 in ENDOK.
    apply sbs_ok_cons_flat in ENDOK. destruct ENDOK as (Rl & ROOM & _).
    call (cb_S6 L s lfc ldl LT (arr_get lfc 256) (arr_get ldl 256) (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) (wz (ds_bi_buf s))).
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ exact ALT. } 1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ lia. } 1:{ exact ROOM. }
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    do 13 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold compress_block_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
  - (* [comment removed for export] *)
    uwalk 0x1da00 CB_TRAP. at_pc 0x1da00.
    rewrite (proj2 (Z.ltb_lt 0 LT)) by lia. cbn [Z.b2z].
    destruct (Z.to_nat (ds_sym_next s)) as [|f] eqn:En; [lia|].
    remember (compress_block_loop (S f) s lfc ldl dfc ddl 0) as R eqn:ER.
    specialize (CBOK K).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      call (cb_loop f L s lfc ldl dfc ddl LT DT R mc (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) 0 (wz (ds_bi_buf s))) end.
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact ALT. } 1:{ exact ADT. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact RBV. } 1:{ lia. } 1:{ exact BYT. }
    1:{ exact Rlb. } 1:{ exact Rsn1. } 1:{ exact Rsn2. } 1:{ lia. } 1:{ lia. } 1:{ rewrite EX0. exact CBOK. } 1:{ rewrite EX0. exact ER. }
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ =>
      assert (EQF : compress_block s lfc ldl dfc ddl
                    = upd4 s (sbF_PB pb pd bb bv (arr_get lfc 256) (arr_get ldl 256)) (sbF_PD pd bv (arr_get ldl 256))
                             (sbF_BB bb bv (arr_get lfc 256) (arr_get ldl 256)) (sbF_BV bv (arr_get ldl 256)));
      [ unfold compress_block; rewrite (proj2 (Z.eqb_neq _ _) K); cbn [negb]; rewrite ?En; rewrite <- ER, E; unfold send_code, END_BLOCK; apply send_bits_sbF |]
    end.
    cbv zeta in ENDOK. rewrite (proj2 (Z.eqb_neq _ _) K) in ENDOK. cbn [negb] in ENDOK. rewrite ?En in ENDOK.
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ => rewrite E in ENDOK end.
    unfold END_BLOCK in ENDOK. apply sbs_ok_cons_flat in ENDOK. destruct ENDOK as (Rl & ROOM & _).
    unfold ucbR.
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ => call (cb_S6 L s lfc ldl LT (arr_get lfc 256) (arr_get ldl 256) pb pd bb bv) end.
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ exact ALT. } 1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ assumption. } 1:{ assumption. } 1:{ exact ROOM. }
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    do 13 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold compress_block_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
Qed.
