(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ITree Nodes Decode SysStep SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import FX_lib. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s I_consts I_qck. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_memcpyw I_memcpy F_achk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require F_fwritex.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Import ListNotations.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition memcpy_posti (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(Dst, Dst + N); (bv_unsigned sp - 2240, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at asegs m' Src src
    /\ stk asegs m' lo (bv_unsigned sp).

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma imemcpy_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte) (lo : Z),
  bytes_at asegs m Src src -> length src = Z.to_nat N -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src) -> (0 <= N) ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2240 -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  (N = 0 \/ Src + N <= lo \/ bv_unsigned sp <= Src) -> (N = 0 \/ Dst + N <= lo \/ bv_unsigned sp <= Dst) ->
  chkr m Src N -> chkr m Dst N -> ictx m -> mem_inv asegs m ->
  evt asegs (memcpy_posti ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x812f4) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros BA LEN DC SEP HN ST LO LOLO SPH SEPS SEPD CS CD IC MI.
  pose proof (chkr_bound m Src N CS) as (S0 & SB). pose proof (chkr_bound m Dst N CD) as (D0 & DB).
  pose proof (chkr_chk_ok m Src N CS) as CHS. pose proof (chkr_chk_ok m Dst N CD) as CHD.
  destruct IC as (ICM & _ & _ & M2S).
  unfold kHighMemEnd, kHighShadowEnd in *.
  assert (EN : Z.of_nat (length src) = N) by (rewrite LEN; lia).
  rewrite <- LEN in DC.
  zstep.
  eapply evt_mono.
  { eapply (imemcpy_spec RIP ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src src junk lo); rewrite ?EN.
    all: first [reflexivity | exact ST | exact BA | exact DC | exact CHS | exact CHD | exact M2S | exact ICM | exact MI | lia
               | unfold kHighShadowEnd; lia]. }
  cbv beta. intros ms' PS. unfold imemcpy_post in PS. rewrite EN in PS.
  destruct PS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST' & DC' & SC').
  unfold memcpy_posti. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
  split; [rewrite <- LEN; exact DC'|]. split; [exact SC'| exact ST'].
Qed.

Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' Fp (file_cells flags wend (wpos + l) wbase wfn bufp bufsize fd mode lbf tail)
    /\ rw_cells asegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
    /\ bytes_at asegs m' S src.

Lemma fwx_tail : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l i lo : Z),
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  rw_cells asegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
  bytes_at asegs m S src -> Z.of_nat (length src) = l ->
  stk asegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64 - 2240) -> (bv_unsigned sp < 2^63) ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
  (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wpos + l <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
  (0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
  kHighShadowEnd + 8 <= lo -> chkr m S l -> chkr m wpos (Z.of_nat cap) -> ictx m ->
  evt asegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1538e4) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI
    HSH CS CB0 IC.
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
  assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  assert (CD : chkr m wpos l) by (apply (chkr_sub m wpos (Z.of_nat cap) wpos l CB0); lia).
  unfold file_cells in FC.

  apply (rw_cells_split_CB asegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
  cbn [mk_CB_cells app] in DST.
  apply (proj1 (F_fwritex.rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
  cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
  step. step. step.
  replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
  assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
  assert (EUf : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  rewrite <- LEN in CS, CD.
  call imemcpy_callw.
  1:{ exact SRC. }
  1:{ rewrite Nat2Z.id. reflexivity. }
  1:{ rewrite Nat2Z.id. exact DSTa. }
  1:{ lia. } 1:{ lia. }
  1:{ rewrite EUf. exact ST. }
  1:{ rewrite EUf. lia. } 1:{ exact HSH. } 1:{ rewrite EUf. lia. }
  1:{ rewrite EUf. lia. } 1:{ rewrite EUf. lia. }
  1:{ exact CS. } 1:{ exact CD. } 1:{ exact IC. } 1:{ exact MI. }
  lazymatch goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))) |- _ => rewrite EUf in H; rename H into ST end.
  rewrite !Nat2Z.id in *.
  do 4 step.
  do 9 step.
  release_frame FR ST (bv_unsigned sp).
  rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST' : rw_cells asegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
      by (apply (proj2 (F_fwritex.rw_cells_app asegs _ _ [_] _)); split; [exact PC|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
  end.
  cbn [app] in DST'. rewrite !LEN in *.
  unfold fwx_ret_post, file_cells. sys_finish.
Qed.

Lemma fwx_fit_plain : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l lo : Z),
  rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  rw_cells asegs m wpos [CB cap junk] -> Z.of_nat cap = wend - wpos ->
  bytes_at asegs m S src -> Z.of_nat (length src) = l ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
  (0 < wend < 2^64) -> (0 <= wpos) -> (l <= wend - wpos) -> (S < 2^64) ->
  (2^31 <= lbf < 2^32) ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2304) -> (0 <= lo) -> (bv_unsigned sp < 2^63) ->
  mem_inv asegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (wend <= lo \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wend <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
  kHighShadowEnd + 8 <= lo -> chkr m S l -> chkr m wpos (Z.of_nat cap) -> ictx m ->
  evt asegs (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1537ec) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI LBF ST LO LO0 SPHI MI Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3
    HSH CS CB0 IC.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf.
  pose proof (wmono_refl asegs m) as WM.
  unfold file_cells in FC.
  carve_frame 64%nat ST.
  zidle_begin sp 64%Z MUz WMz.
  do 8 step.
  zidle_end MUz WMz.
  do 5 step.
  if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
  do 3 step.
  if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
  do 3 step.
  pose proof (F_fwritex.sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
  specialize (NEG ltac:(lia)).
  if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CSm : chkr mm S l) by (apply (chkr_munch _ m mm S l CS MUf); intros x Hx; cbn [outside];
                                   unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia);
    assert (CBm : chkr mm wpos (Z.of_nat cap)) by (apply (chkr_munch _ m mm wpos _ CB0 MUf); intros x Hx; cbn [outside];
                                   unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia);
    assert (ICm : ictx mm) by (apply (ictx_munch _ m mm IC MUf ltac:(assumption)); intros x Hx; cbn [in_rl ICR outside] in *;
                                   unfold kHighShadowEnd in *; lia)
  end.
  eapply fwx_tail; [exact FR | exact FC | exact DST | lia | exact SRC | exact LEN | exact ST | lia | lia | exact MU | exact WM | exact MI | lia ..
                   | exact HSH | exact CSm | exact CBm | exact ICm ].
Qed.
End WithRIP.
