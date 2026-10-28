(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge Frame TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap ECH_Xpres AsWalk.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wins_hi_tac := unfold wins_hi; repeat (apply Forall_cons; [cbn [fst snd]; acb; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac acc_bounds :=
  repeat match goal with
  | A : accessible _ ?a ?n |- _ =>
      lazymatch goal with
      | _ : a + n <= AAPP_HI |- _ => fail
      | _ => pose proof (proj1 (proj2 A) : a + n <= AAPP_HI)
      end
  end.

Ltac hlia := first [ lia | acc_bounds; acb; unfold aapp, aapp_lo, aapp_hi, AAPP_HI, AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia ].

Ltac transport_shadow_hi m m' MUc WMc :=
  let W := lazymatch type of MUc with munch ?W _ _ => W end in
  repeat match goal with
  | Hh : accessible m ?a ?n |- _ =>
      first [ apply (AsWalk.accessible_transport_hi W m m' a n) in Hh; [| exact MUc| wins_hi_tac]
            | idtac "note: dropping shadow fact (footprint not provably high):" Hh; clear Hh ]
  | Hh : addressable m ?a ?n |- _ =>
      first [ apply (AsWalk.addressable_transport_hi W m m' a n) in Hh; [| exact MUc| exact WMc| hlia| wins_hi_tac]
            | idtac "note: dropping shadow fact (footprint not provably high):" Hh; clear Hh ]
  | Hh : SHAD m ?a ?sbs |- _ =>
      first [ apply (AsWalk.SHAD_transport_hi W m m' a sbs) in Hh; [| exact MUc| exact WMc| cbn [length]; hlia| wins_hi_tac]
            | idtac "note: dropping shadow fact (footprint not provably high):" Hh; clear Hh ]
  | Hh : shvis m ?lo ?hi |- _ =>
      first [ apply (AsWalk.shvis_transport_hi W m m' lo hi) in Hh; [| exact MUc| exact WMc| hlia| hlia| wins_hi_tac]
            | idtac "note: dropping shadow fact (footprint not provably high):" Hh; clear Hh ]
  end.

Ltac acall_post segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in
  destruct PO as [E PO]; subst ms';
  try destruct_ands PO;
  (* [comment removed for export] *)
  lazymatch goal with
  | MUc : munch _ m ?m', WMc : wmono segs m ?m' |- _ =>
      unfold AINTRIN_STACK, AFS_STACK in MUc; rewrite ?unsigned_lit in MUc by lia;
      transport_after_call segs m m' MUc WMc;
      transport_shadow_hi m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try match goal with H : ACONST m |- _ => clear H end;
      try clear m;
      try (lazymatch goal with H : mem_inv segs m' |- _ => rename H into MI end);
      try (lazymatch goal with H : ACONST m' |- _ => rename H into AC end);
      try (lazymatch goal with H : stk segs m' _ _ |- _ => rename H into ST end)
  end;
  repeat match goal with
  | Hq : context [bv_unsigned (Z_to_bv 64 (bv_unsigned _ + _))] |- _ => rewrite unsigned_lit in Hq by lia
  end;
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "acall" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | acall_post segs m ]
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition amove_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SP Dst Src N : Z) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(Dst, Dst + N); (SP - 4096, SP)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
    /\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at asegs m' Src src
    /\ ACONST m'.

Section CallsZ.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma asan_memcpy_specZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (SP Dst Src N : Z) (src junk : list byte) (lo : Z),
    bytes_at asegs m Src src -> length src = Z.to_nat N -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] ->
    (Src + N <= Dst \/ Dst + N <= Src) -> 0 <= N <= 2^40 -> 0 <= Src -> 0 <= Dst ->
    accessible m Src N -> accessible m Dst N -> shvis m Src (Src + N) -> shvis m Dst (Dst + N) ->
    in_app_mem Src (Src + N) -> in_app_mem Dst (Dst + N) -> aconst_ok (Dst, Dst + N) ->
    stk asegs m lo SP -> aceil <= lo -> lo <= SP - 4096 -> SP < 2^64 ->
    (Dst + N <= lo \/ SP <= Dst) -> (Src + N <= lo \/ SP <= Src) ->
    mem_inv asegs m -> ACONST m ->
    evt asegs (amove_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP Dst Src N src lo m)
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AASAN_MEMCPY) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros SRC LEN DST SEP HN HS HD ACS ACD SVS SVD IMS IMD AOK ST CE LO SPH FSD FSS MI AC.
    pose proof ACS as (_ & SH' & _). pose proof ACD as (_ & DH' & _). unfold AAPP_HI in SH', DH'.
    assert (SP0 : 0 <= SP) by (destruct ST as [? _]; lia).
    eapply evt_mono.
    { eapply (ah_memcpy H HH) with (lo := lo); rewrite ?unsigned_lit by lia; try eassumption; unfold AINTRIN_STACK; lia. }
    intros ms' PO. cbv beta in PO. unfold amemcpy_post in PO. unfold amove_post.
    rewrite !(unsigned_lit Dst), !(unsigned_lit Src), !(unsigned_lit N), !(unsigned_lit SP) in PO by lia. unfold AINTRIN_STACK in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU' & WM' & MI' & ST' & D' & S' & AC').
    do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact AC'.
  Qed.

  Lemma asan_memmove_specZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (SP Dst Src N : Z) (src junk : list byte) (lo : Z),
    bytes_at asegs m Src src -> length src = Z.to_nat N -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] ->
    (Src + N <= Dst \/ Dst + N <= Src) -> 0 <= N <= 2^40 -> 0 <= Src -> 0 <= Dst ->
    accessible m Src N -> accessible m Dst N -> shvis m Src (Src + N) -> shvis m Dst (Dst + N) ->
    in_app_mem Src (Src + N) -> in_app_mem Dst (Dst + N) -> aconst_ok (Dst, Dst + N) ->
    stk asegs m lo SP -> aceil <= lo -> lo <= SP - 4096 -> SP < 2^64 ->
    (Dst + N <= lo \/ SP <= Dst) -> (Src + N <= lo \/ SP <= Src) ->
    mem_inv asegs m -> ACONST m ->
    evt asegs (amove_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP Dst Src N src lo m)
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AASAN_MEMMOVE) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros SRC LEN DST SEP HN HS HD ACS ACD SVS SVD IMS IMD AOK ST CE LO SPH FSD FSS MI AC.
    pose proof ACS as (_ & SH' & _). pose proof ACD as (_ & DH' & _). unfold AAPP_HI in SH', DH'.
    assert (SP0 : 0 <= SP) by (destruct ST as [? _]; lia).
    eapply evt_mono.
    { eapply (ah_memmove H HH) with (lo := lo); rewrite ?unsigned_lit by lia; try eassumption; unfold AINTRIN_STACK; lia. }
    intros ms' PO. cbv beta in PO. unfold amemmove_post in PO. unfold amove_post.
    rewrite !(unsigned_lit Dst), !(unsigned_lit N), !(unsigned_lit SP) in PO by lia. unfold AINTRIN_STACK in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU' & WM' & MI' & ST' & D' & AC').
    do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]).
    split; [| exact AC']. eapply bytes_at_transport; [exact SRC| exact MU'|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Definition amemset_postZ (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (SP Dst C N : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(Dst, Dst + N); (SP - 4096, SP)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
      /\ rw_cells asegs m' Dst [CB (Z.to_nat N) (poison_bytes (Z.to_nat N) C)]
      /\ ACONST m'.

  Lemma asan_memset_specZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (SP Dst C N : Z) (junk : list byte) (lo : Z),
    0 <= C < 256 -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] -> 0 <= N <= 2^40 -> 0 <= Dst ->
    accessible m Dst N -> shvis m Dst (Dst + N) -> in_app_mem Dst (Dst + N) -> aconst_ok (Dst, Dst + N) ->
    stk asegs m lo SP -> aceil <= lo -> lo <= SP - 4096 -> SP < 2^64 ->
    (Dst + N <= lo \/ SP <= Dst) ->
    mem_inv asegs m -> ACONST m ->
    evt asegs (amemset_postZ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP Dst C N lo m)
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AASAN_MEMSET) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HC DST HN HD ACD SVD IMD AOK ST CE LO SPH FSD MI AC.
    pose proof ACD as (_ & DH' & _). unfold AAPP_HI in DH'.
    assert (SP0 : 0 <= SP) by (destruct ST as [? _]; lia).
    eapply evt_mono.
    { eapply (ah_memset H HH) with (lo := lo); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; unfold AINTRIN_STACK; lia. }
    intros ms' PO. cbv beta in PO. unfold amemset_post in PO. unfold amemset_postZ.
    rewrite !(unsigned_lit Dst), !(unsigned_lit N), !(unsigned_lit SP) in PO by lia. unfold AINTRIN_STACK in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU' & WM' & MI' & ST' & D' & AC').
    do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact AC'.
  Qed.
End CallsZ.
