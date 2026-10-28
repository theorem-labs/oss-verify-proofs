(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcfmt I_vprintfw I_vsntail I_vsnstmt I_pcxlist F_achk.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
(* [comment removed for export] *)
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u32arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u64arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8ro segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.

(* [comment removed for export] *)
Notation IVSNW_DEPTH := 4480 (only parsing).
(* [comment removed for export] *)
Notation IVFW_DEPTH := 2368 (only parsing).

(* [comment removed for export] *)
Definition vsncells (m : mem) : Prop := ro_cells ctasegs m 0x5ac328 [C8 (Z_to_bv 64 0x529f68)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pcg_ok (body : list Z) (args : list parg) (slots : list word) (A VA lo bnd : Z) (m : mem) : Prop :=
  pcomx_ok (body ++ [0]) args = true /\ Forall (fun c => 0 < c < 256) body /\ (1 <= length body)%nat
  /\ bytes_at ctasegs m A (zb8 (body ++ [0])) /\ A + Z.of_nat (length body) + 3 <= lo /\ 1 <= A
  /\ chk_ok m A (Z.of_nat (length body) + 1)
  /\ (forall i w, nth_error slots i = Some w -> ro_cells ctasegs m (VA + 8 * Z.of_nat i) [C8 w])
  /\ bnd <= VA /\ VA + 8 * Z.of_nat (length slots) + 16 < 2^63
  /\ (exists cin, ck_args m lo bnd slots args (pcx_covs (length (body ++ [0])) (body ++ [0]) args cin))
  /\ pctx m /\ pfcells m.

Lemma ck_args_xfer : forall m m' lo bnd bnd' slots args covs,
  ck_args m lo bnd slots args covs -> bnd' <= bnd -> kHighShadowEnd + 8 <= lo ->
  agree_on (fun x => x < lo \/ bnd <= x) m m' -> ck_args m' lo bnd' slots args covs.
Proof.
  intros m m' lo bnd bnd' slots args. revert slots.
  induction args as [|a args IH]; intros slots covs H LE LOLO AG; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH _ _ H2 LE LOLO AG)].
  unfold kHighShadowEnd in LOLO. destruct a; cbn [ck_arg] in H1 |- *; try exact H1.
  destruct (vhd_cov covs); [exact I|].
  destruct H1 as (str & CS & P0 & SEP & HI & CK). exists str. split; [| split; [exact P0| split; [lia| split; [exact HI|]]]].
  - apply (cstr_agree m m' _ _ CS). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn beta. lia.
  - eapply chkr_agree; [exact CK |]. apply (agree_sub _ _ _ _ AG). intros x Hx. cbn beta. unfold SHADOW_LO, SHADOW_HI in Hx. lia.
Qed.

Lemma pcg_ok_xfer : forall W body args slots A VA lo bnd bnd' m m',
  pcg_ok body args slots A VA lo bnd m -> lo <= bnd' <= bnd -> bnd <= 2^47 -> kHighShadowEnd + 8 <= lo ->
  munch W m m' -> wmono ctasegs m m' -> (forall x, x < lo \/ bnd <= x -> outside W x) ->
  pcg_ok body args slots A VA lo bnd' m'.
Proof.
  intros W body args slots A VA lo bnd bnd' m m' (OK & FB & L1 & BY & AB & A1 & CHKA & VS & QVA & VAH & CKA & PCX & PFC) LE B47 LOLO MU WM HW.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO.
  pose proof (agree_of_munch _ _ _ (fun x => x < lo \/ bnd <= x) MU HW) as AG.
  split; [exact OK|]. split; [exact FB|]. split; [exact L1|]. split.
  { apply (bytes_at_agree ctasegs m m' _ _ BY). apply (agree_sub _ _ _ _ AG). intros x Hx. rewrite length_zb8, length_app in Hx. cbn [length] in Hx. cbn beta. lia. }
  split; [exact AB|]. split; [exact A1|]. split.
  { eapply chk_ok_agree; [exact CHKA | lia | lia |]. apply (agree_sub _ _ _ _ AG). intros x Hx. cbn beta. lia. }
  split.
  { intros i w Hn. apply (ro_cells_agree ctasegs m m' _ _ (VS i w Hn)). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn beta. lia. }
  split; [lia|]. split; [exact VAH|]. split.
  { destruct CKA as [cin CKA]. exists cin. apply (ck_args_xfer m m' lo bnd bnd' slots args _ CKA ltac:(lia) LOLO'). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn beta. lia. }
  split.
  - apply (pctx_munch _ m m' PCX MU WM). intros x Hx. apply HW. unfold in_PCR in Hx. lia.
  - apply (pfcells_munch _ m m' PFC MU WM). intros x Hx. apply HW. unfold in_PFR in Hx. lia.
Qed.

(* [comment removed for export] *)
Local Definition pbox (P : Prop) : Prop := P.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ivsnA_post (usp D n A VA : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j8 junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x1b2568) (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 A)
                  (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7 (Z_to_bv 64 D) (Z_to_bv 64 n)
                  (Z_to_bv 64 0x703b68) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x529f68) fc None m' (seg_rom ctasegs)
    /\ munch [(usp - IVSNW_DEPTH, usp)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (usp + -2160)
    /\ rw_cells ctasegs m' (usp + -96) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
                                      C8 s1; C8 s0; C8 ra]
    /\ rw_cells ctasegs m' (usp + -2160) [CB 2064 junk].

(* [comment removed for export] *)
Lemma ivsn_walkA' : forall (usp D n A VA lo : Z) (body : list Z) (args : list parg) (slots : list word)
    ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk ctasegs m lo usp -> lo <= usp - IVSNW_DEPTH -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
  0 <= D < 2^64 -> 0 <= n < 2^64 ->
  pcg_ok body args slots A VA lo usp m -> vsncells m -> mem_inv ctasegs m ->
  evt ctasegs (ivsnA_post usp D n A VA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b24d4) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH S16 D0 N0 PCG VSN MI.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - IVSNW_DEPTH, usp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  pose proof PCG as (OK & FB & L1 & BY & AB & A1 & CHKA & VS & QVA & VAH & CKA & PCX & PFC).
  pose proof (bytes_at_bound _ _ _ _ BY) as AB0. rewrite length_zb8, length_app in AB0. cbn [length] in AB0.
  destruct PFC as (AI & GCF & CPF & RVP & RVF). unfold vsncells in VSN.
  clear BY VS CKA PCX. change (pbox (pcg_ok body args slots A VA lo usp m)) in PCG.
  carve_frame 96%nat ST. rename FR into FRt.
  carve_frame 2064%nat ST. rename FR into FRb.
  apply (rw_cells_split_CB ctasegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRt; [| reflexivity].
  cbn [mk_CB_cells app] in FRt.
  zidle_beginz usp 2160%Z MUz1 WMz1.
  zhide.
  xsteps_to 0x1cb8c8%Z.
  zidle_end MUz1 WMz1.
  call try_init_spec; [exact AI | rewrite EU2160; exact ST | rewrite EU2160; lia | lia | assumption |].
  xsteps_to 0x1b1958%Z.
  rename POST into ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (PCG1 : pcg_ok body args slots A VA lo (usp + -2160) mm) by
      (unfold pbox in PCG; eapply (pcg_ok_xfer _ body args slots A VA lo usp (usp + -2160) m mm PCG); [lia | lia | exact LOLO' | exact MU | exact WM
        | intros ?x ?Hx; cbn [outside]; lia]) end.
  pose proof PCG1 as (_ & _ & _ & BY1 & _ & _ & CHKA1 & VS1 & _ & _ & (cin1 & CKA1) & PCX1 & _). clear PCG1.
  call (pcom_genx_spec RIP A body args cin1 VA lo slots);
    [ reflexivity | reflexivity | exact OK | exact FB | exact L1 | exact BY1 | lia | lia | exact VS1 | rewrite EU2160; lia | lia
    | rewrite EU2160; exact CKA1
    | exact ST | rewrite EU2160; lia | exact LOLO' | rewrite EU2160; lia
    | rewrite EU2160; Z.div_mod_to_equations; lia | exact CHKA1 | exact PCX1 | assumption | ].
  try clear BY1; try clear CHKA1; try clear VS1; try clear CKA1; try clear PCX1. rename POST into ST. rewrite EU2160 in ST.
  xsteps_to 0x529f68%Z.
  apply evt_done. unfold ivsnA_post. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRt| exact FRb].
Qed.

(* [comment removed for export] *)
Lemma ivsn_walkA : forall (usp D n A VA lo : Z) (body : list Z) (args : list parg) (slots : list word)
    ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk ctasegs m lo usp -> lo <= usp - IVSNW_DEPTH -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
  0 <= D < 2^64 -> 0 <= n < 2^64 ->
  pcg_ok body args slots A VA lo usp m -> vsncells m -> mem_inv ctasegs m ->
  evt ctasegs (ivsnA_post usp D n A VA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ad66c) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH S16 D0 N0 PCG VSN MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  lstep.
  apply (ivsn_walkA' usp D n A VA lo body args slots); assumption.
Qed.

(* [comment removed for export] *)
Lemma ivsn_walkC : forall (usp D n r lo : Z) (j8 junk : list byte)
    (ra' ra gp tp t0 t1 t2 s0 s1 s1' s2 s3 s4 s5 s6 s7 s4' s5' s6' s7' s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VAw : word)
    F fc (m : mem),
  stk ctasegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 ->
  rw_cells ctasegs m (usp + -96) [C8 VAw; C8 VAw; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells ctasegs m (usp + -2160) [CB 2064 junk] ->
  0 <= r -> r < n -> r + 1 < 2^31 -> n < 2^63 -> 0 <= D -> D + r + 1 < 2^47 ->
  chk_ok m D (r + 1) -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(usp - 2240, usp)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1' (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) (Z_to_bv 64 n) s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b2568) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH FRt FRb R0 RN RH NH D0 DH CHK M2S MI.
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - 2240, usp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ESr : bv_signed (Z_to_bv 64 r) = r).
  { unfold bv_signed. rewrite EUr. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia. }
  zhide.
  lstep. if_false.
  lstep. lstep. lstep.
  rewrite (bv_swrap_small 32 (r + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  if_true.
  lstep. lstep. rewrite (lxor_ones64 D) by lia.
  assert (EUnd : bv_unsigned (Z_to_bv 64 (18446744073709551615 - D)) = 18446744073709551615 - D) by (apply unsigned_lit; lia).
  lstep. lstep. lstep. if_true.
  eapply evt_cut.
  { apply (ivsn_chk RIP usp D n (r + 1) r); first [exact ST | exact CHK | exact M2S | exact MI | lia | (unfold kHighShadowEnd; lia)]. }
  cbv beta. intros ms' P. unfold ivsn_pre_epi in P.
  destruct P as (m1 & ra1 & u0 & u1 & u2 & u3 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & -> & MU1 & WM1 & MI1 & ST1).
  pose proof (rw_cells_transport ctasegs _ _ _ _ _ FRt MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRt1.
  pose proof (rw_cells_transport ctasegs _ _ _ _ _ FRb MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRb1.
  clear FRt FRb ST. rename ST1 into ST.
  assert (MU2 : munch [(usp - 2240, usp)] m m1)
    by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia).
  assert (WM2 : wmono ctasegs m m1) by exact (wmono_trans _ _ _ _ WM WM1).
  clear MU MU1 WM WM1. rename MU2 into MU. rename WM2 into WM.
  lstep.
  release_frame FRb1 ST (usp + -96).
  do 11 lstep.
  release_frame FRt1 ST usp.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ivfA_post (usp Fp A VA : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR (Z_to_bv 64 0x1b2490) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 Fp)
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA) a3 a4 a5 a6 a7 (Z_to_bv 64 VA) s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x526dec) fc None m' (seg_rom ctasegs)
    /\ munch [(usp - IVFW_DEPTH, usp)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (usp + -48)
    /\ rw_cells ctasegs m' (usp + -48) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ivfsn_walkA : forall (usp Fp A VA lo : Z) (body : list Z) (args : list parg) (slots : list word)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk ctasegs m lo usp -> lo <= usp - IVFW_DEPTH -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 -> 0 <= Fp < 2^64 ->
  pcg_ok body args slots A VA lo usp m -> mem_inv ctasegs m ->
  evt ctasegs (ivfA_post usp Fp A VA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ad668) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH S16 FP0 PCG MI.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - IVFW_DEPTH, usp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof PCG as (OK & FB & L1 & BY & AB & A1 & CHKA & VS & QVA & VAH & CKA & PCX & PFC).
  pose proof (bytes_at_bound _ _ _ _ BY) as AB0. rewrite length_zb8, length_app in AB0. cbn [length] in AB0.
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  clear BY VS CKA PCX. change (pbox (pcg_ok body args slots A VA lo usp m)) in PCG.
  carve_frame 48%nat ST. rename FR into FRf.
  apply (rw_cells_split_CB ctasegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRf; [| reflexivity]. cbn [mk_CB_cells app] in FRf.
  zhide.
  xsteps_to 0x1cb8c8%Z.
  call try_init_spec; [exact AI | rewrite EU48; exact ST | rewrite EU48; lia | lia | assumption |].
  xsteps_to 0x1b1958%Z.
  rename POST into ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (PCG1 : pcg_ok body args slots A VA lo (usp + -48) mm) by
      (unfold pbox in PCG; eapply (pcg_ok_xfer _ body args slots A VA lo usp (usp + -48) m mm PCG); [lia | lia | exact LOLO' | exact MU | exact WM
        | intros ?x ?Hx; cbn [outside]; lia]) end.
  pose proof PCG1 as (_ & _ & _ & BY1 & _ & _ & CHKA1 & VS1 & _ & _ & (cin1 & CKA1) & PCX1 & _). clear PCG1.
  call (pcom_genx_spec RIP A body args cin1 VA lo slots);
    [ reflexivity | reflexivity | exact OK | exact FB | exact L1 | exact BY1 | lia | lia | exact VS1 | rewrite EU48; lia | lia
    | rewrite EU48; exact CKA1
    | exact ST | rewrite EU48; lia | exact LOLO' | rewrite EU48; lia
    | rewrite EU48; Z.div_mod_to_equations; lia | exact CHKA1 | exact PCX1 | assumption | ].
  try clear BY1; try clear CHKA1; try clear VS1; try clear CKA1; try clear PCX1. rename POST into ST. rewrite EU48 in ST.
  xsteps_to 0x526dec%Z.
  apply evt_done. unfold ivfA_post. do 13 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FRf.
Qed.
End WithRIP.

(* [comment removed for export] *)
Lemma ivfsn_walkB : forall (usp VA lo : Z)
    (ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk ctasegs m lo (usp + -48) -> lo <= usp + -48 -> usp <= 2^47 ->
  rw_cells ctasegs m (usp + -48) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv ctasegs m ->
  evt ctasegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom ctasegs))
                 /\ stk ctasegs m lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b2490) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros ST LO UT FRf MI.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  zhide.
  do 6 lstep.
  release_frame FRf ST usp.
  apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.
