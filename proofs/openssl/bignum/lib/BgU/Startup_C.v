(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Str_tac InitMem Startup_glue Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import F_memset F_memcpy Startup_B Startup_A.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.

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

Local Ltac zidle_end_m MUz :=
  let fp := type of MUz in
  match fp with munch _ ?m0 ?m1 =>
    match goal with GR : wmono bgusegs m0 m1 |- _ =>
      repeat match goal with ZD : zidle _ |- _ => unfold zidle in ZD end;
      transport_after_call bgusegs m0 m1 MUz GR; clear MUz GR
    end
  end.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].

Notation bgusegs := ImageBg.bgusegs.

Section InitLibc.
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (E : Z) (eps : list word) (R : Z) (g : word) (uid hw : word) (P : Z) (s : list byte)
            (pn0 pnf0 hw0 env0 : word) (gjunk : list byte).
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x350fa0); (0x350fa8, 0x350fd8);
                 (RGUARD, 0x350fe0); (RPROGNAME, 0x351228); (RLIBC, 0x351298)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

  Definition init_libc_post : Z -> machine_state -> Prop :=
    fun tid st =>
      exists (m' : word -> option byte) (pg r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word),
        st = MS (mkR ra sp gp (Z_to_bv 64 0x330f98) r5 r6 r7 s0 s1 r10 r11 r12 r13 r14 r15 r16 r17
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r28 r29 r30 r31)
                F (ret_pc ra) fc None m' (seg_rom bgusegs)
        /\ munch W m m'
        /\ wmono bgusegs m m'
        /\ mem_inv bgusegs m'
        /\ stk bgusegs m' lo (bv_unsigned sp)
        /\ (0 < tid < 4194304)%Z
        /\ rw_cells bgusegs m' 0x351218 [C8 pg; C8 (Z_to_bv 64 P)]
        /\ rw_cells bgusegs m' 0x351228
             (libc_cells (Z_to_bv 8 1) (Z_to_bv 64 AUXV) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 4096))
        /\ rw_cells bgusegs m' 0x351290 [C8 hw]
        /\ rw_cells bgusegs m' 0x330ec8 [C8 (Z_to_bv 64 E)]
        /\ rw_cells bgusegs m' 0x330ed0
             (rtd_cells (Z_to_bv 64 0x330ed0) (Z_to_bv 64 0x330ed0) (Z_to_bv 64 0x330ed0) z64
                        (Z_to_bv 64 tid) z64 (Z_to_bv 64 2) (Z_to_bv 64 0x330f48) (Z_to_bv 64 0x351260)
                        (guard_of g) (Z_to_bv 64 0x330fa8) z64)
        /\ rw_cells bgusegs m' 0x350fa0 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
        /\ rw_cells bgusegs m' 0x350fd8 [C8 (guard_of g)]
        /\ bytes_at bgusegs m' R (le8 g)
        /\ bytes_at bgusegs m' P (s ++ [Z_to_bv 8 0])
        /\ bytes_at bgusegs m' E (u64s eps ++ le8 z64 ++ u64s (auxv20 (Z_to_bv 64 R) uid hw))
        /\ rw_cells bgusegs m' RSYSINFO [C8 z64]
        /\ rw_cells bgusegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
        /\ rw_cells bgusegs m' RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x351220); C8 (Z_to_bv 64 RPROGNAME)]
        /\ rw_cells bgusegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
        /\ rw_cells bgusegs m' RGOT_DYNAMIC [C8 z64].

  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (0x353000 <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.

  Definition pn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte)
    : machine_state -> Prop :=
    fun st =>
      exists (pg : word) (m1 : word -> option byte),
        st = MS (mkR (Z_to_bv 64 0x2b0240) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7 (Z_to_bv 64 P) x9
                     (Z_to_bv 64 0x351218) (Z_to_bv 64 (P + (Z.of_nat (length s) + 1))) (Z_to_bv 64 47) z64
                     x14 x15 x16 x17 (Z_to_bv 64 0x351228) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x2b031c) fc None m1 (seg_rom bgusegs)
        /\ munch [(0x351218, 0x351220)]%Z m0 m1
        /\ wmono bgusegs m0 m1
        /\ mem_inv bgusegs m1
        /\ rw_cells bgusegs m1 0x351218 [C8 pg; C8 (Z_to_bv 64 P)]
        /\ bytes_at bgusegs m1 P (s ++ [Z_to_bv 8 0]).

  Lemma pn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
    (Z.of_nat k = Z.of_nat (length s) + 1 - j)%Z -> (1 <= j)%Z ->
    munch [(RPROGNAME, 0x351220)]%Z m0 mm -> wmono bgusegs m0 mm -> mem_inv bgusegs mm ->
    bytes_at bgusegs mm P (s ++ [Z_to_bv 8 0]) ->
    rw_cells bgusegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
    evt bgusegs (pn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
      (MS (mkR (Z_to_bv 64 0x2b0240) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
               (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
               (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2b0310) fc None mm (seg_rom bgusegs)).
  Proof using NONUL LO LOLO SPP.
    induction k as [|k IHk];
      intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg CNT JPOS FOOT GROW MINV STR PGC.
    - assert (JEND : j = (Z.of_nat (length s) + 1)%Z) by lia.
      subst j.
      pose proof (bytes_at_read bgusegs mm P (s ++ [Z_to_bv 8 0]) (Z.of_nat (length s)) 1 STR ltac:(lia)
                    ltac:(rewrite length_app; cbn [length]; lia)) as BYTE.
      rewrite Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag in BYTE. cbn [firstn skipn app] in BYTE.
      let a := cur_mem_addr in replace (wa (P + Z.of_nat (length s))) with a in BYTE by (unfold wa; f_equal; lia).
      lstep. clear BYTE. astep. astep.
      apply evt_done. exists pg, mm.
      split; [cbv delta [mkR]; reflexivity|].
      repeat (split; [assumption|]). assumption.
    - destruct (nth_error s (Z.to_nat (j - 1))) as [ch|] eqn:NTH.
      2:{ apply nth_error_None in NTH. lia. }
      assert (CHNZ : bv_unsigned ch <> 0%Z).
      { exact (proj1 (Forall_forall _ s) NONUL ch (nth_error_In s _ NTH)). }
      apply nth_error_split in NTH as (front & back & SPLIT & FLEN).
      pose proof (bytes_at_read bgusegs mm P (s ++ [Z_to_bv 8 0]) (j - 1) 1 STR ltac:(lia)
                    ltac:(rewrite length_app; cbn [length]; lia)) as BYTE.
      rewrite SPLIT, <- app_assoc, <- FLEN, skipn_app, skipn_all, Nat.sub_diag in BYTE.
      cbn [firstn skipn app] in BYTE.
      let a := cur_mem_addr in replace (wa (P + (j - 1))) with a in BYTE by (unfold wa; f_equal; lia).
      lstep. clear BYTE. cbv beta.
      pose proof (byte_range ch) as CHRANGE.
      lstep. rewrite bv_eqb_Z, !unsigned_lit by lia.
      destruct (Z.eqb_spec (bv_unsigned ch) 47) as [SLASH|PLAIN]; cbv iota.
      + lstep. lstep.
        replace (Z_to_bv 64 (P + j + 1)) with (Z_to_bv 64 (P + (j + 1))) by (f_equal; lia).
        eapply IHk; try eassumption; lia.
      + lstep. rewrite bv_eqb_Z, !unsigned_lit by lia.
        rewrite (proj2 (Z.eqb_neq _ _) CHNZ). cbv beta iota delta [negb].
        lstep.
        replace (Z_to_bv 64 (P + j + 1)) with (Z_to_bv 64 (P + (j + 1))) by (f_equal; lia).
        eapply IHk; try eassumption; lia.
  Qed.

  Ltac scan_it AUXB vi ki :=
    lstep; if_false; ldaux AUXB vi; lstep; lstep;
    (try lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?spv + -336 + ?c)] =>
      let off := eval vm_compute in (-336 + c)%Z in
      replace (Z_to_bv 64 (bv_unsigned spv + -336 + c)) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    (try lazymatch goal with |- context [Z_to_bv 64 (?c + (bv_unsigned ?spv + -336))] =>
      let off := eval vm_compute in (c + -336)%Z in
      replace (Z_to_bv 64 (c + (bv_unsigned spv + -336))) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    lstep; lstep; ldaux AUXB ki; lstep; astep.

  Lemma init_libc_spec : forall tp a0 a1,
    stk bgusegs m lo (bv_unsigned sp) ->
    bytes_at bgusegs m E (u64s eps ++ le8 z64 ++ u64s (auxv20 (Z_to_bv 64 R) uid hw)) ->
    bytes_at bgusegs m P (s ++ [Z_to_bv 8 0]) ->
    bytes_at bgusegs m R (le8 g) ->
    rw_cells bgusegs m RPROGNAME [C8 pn0; C8 pnf0] ->
    rw_cells bgusegs m RHWCAP [C8 hw0] ->
    rw_cells bgusegs m RENVIRON [C8 env0] ->
    rw_cells bgusegs m RSYSINFO [C8 z64] ->
    rw_cells bgusegs m RLIBC (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) ->
    rw_cells bgusegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
    rw_cells bgusegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
    rw_cells bgusegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells bgusegs m RGUARD [CB 8 gjunk] ->
    rw_cells bgusegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x351220); C8 (Z_to_bv 64 RPROGNAME)] ->
    rw_cells bgusegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
    rw_cells bgusegs m RGOT_DYNAMIC [C8 z64] ->
    mem_inv bgusegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    impl bgusegs (at_node bgusegs) (enode NSetTid dec_set_tid) (epost init_libc_post)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b0214) fc None m (seg_rom bgusegs)).
  Proof using EPS NONUL LO LOLO SPE SPP SPR.
    intros tp a0 a1 STK ENVB PNB RNDB PGC HWC ENVC SYSC LIBC TDC MTLS DSTK GRD GOT3 GOTG GDUM MINV A0 A1.
    subst a0 a1.
    unfold libc_cells in LIBC. unfold td_cells in TDC.
    pose proof ENVB as AUXB.
    apply bytes_at_app in AUXB as [_ AUXB]. apply bytes_at_app in AUXB as [_ AUXB].
    rewrite u64s_length, length_le8 in AUXB.
    replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
    pose proof (munch_refl W m) as FOOT. pose proof (wmono_refl bgusegs m) as GROW.
    pose proof (bv_unsigned_in_range 64 sp) as SPRANGE. change (bv_modulus 64) with (2 ^ 64)%Z in SPRANGE.
    pose proof (bytes_at_bound _ _ _ _ PNB) as PBOUND. rewrite length_app in PBOUND. cbn [length] in PBOUND.
    iprefix.
    carve_frame 384%nat STK.
    zidle_begin sp 448%Z MUz WMz.
    unfold zidle in AUXB.
    lstep. lstep. lstep. lstep. lstep.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR as [FRLOW FRSAVE].
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [48%nat; 304%nat]) in FRLOW; [|reflexivity].
    cbn [mk_CB_cells app] in FRLOW.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FRLOW as [FRPAD AUXA].
    cbn [cells_size csize Nat.add] in AUXA, FRSAVE.
    change (Z.of_nat 48) with 48%Z in AUXA. change (Z.of_nat 352) with 352%Z in FRSAVE.
    replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUXA by lia.
    replace (bv_unsigned sp + -384 + 352)%Z with (bv_unsigned sp + -32)%Z in FRSAVE by lia.
    lstep. lstep. lstep. lstep. lstep. lstep.
    call (memset_specZ (bv_unsigned sp + -336) 304 0);
      [exact AUXA | assumption | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
    rename POST into AUXZ. change (Z.to_nat 304) with 304%nat in AUXZ.
    zidle_end MUz WMz.
    lstep. lstep. lstep.
    eapply (envp_count_loop eps); [exact EPS | exact ENVB | ].
    lstep. lstep. lstep.
    ldaux AUXB 0%nat. astep.
    lstep. lstep. lstep. lstep.
    zidle_begin sp 448%Z MUa WMa.
    unfold zidle in AUXB.
    scan_it AUXB 1%nat 2%nat. scan_it AUXB 3%nat 4%nat. scan_it AUXB 5%nat 6%nat.
    scan_it AUXB 7%nat 8%nat. scan_it AUXB 9%nat 10%nat. scan_it AUXB 11%nat 12%nat.
    scan_it AUXB 13%nat 14%nat. scan_it AUXB 15%nat 16%nat. scan_it AUXB 17%nat 18%nat.
    lstep. lstep.
    zidle_end_m MUa.
    lstep. lstep. astep.
    lstep. lstep. lstep.
    rewrite bv_eqb_Z, !unsigned_lit by lia. rewrite (proj2 (Z.eqb_neq P 0)) by lia. cbv beta iota delta [negb].
    lstep.
    rewrite bv_eqb_Z, !unsigned_lit by lia. rewrite (proj2 (Z.eqb_neq P 0)) by lia. cbv beta iota delta [negb].
    lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
    call (pn_loop (length s) 1 m0 m0);
      [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact PNB | exact PGC | ].
    lstep. lstep.
    pose proof AUXZ as PHDRS.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in PHDRS as [_ PHDRS].
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in PHDRS as [PHDRS _].
    cbn [cells_size csize Nat.add] in PHDRS. change (Z.of_nat 24) with 24%Z in PHDRS.
    rename PC into PGC. clear POST.
    name_sp sp (-384)%Z.
    icallk (init_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- _ => unname_sp; rewrite ?unsigned_lit by lia; first [ hyp_by_addr | lia ]
         end.
    ipost bgusegs. unname_sp.
    rename PC into STK. rename PC0 into TDC. rename PC1 into LIBC. rename PC2 into MTLS.
    clear PC3 PC4 PC5. unfold libc_cells in LIBC.
    lstep. lstep.
    name_sp sp (-384)%Z.
    call (init_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R g).
    all: lazymatch goal with
         | |- evt _ _ _ => idtac
         | |- _ => unname_sp; rewrite ?unsigned_lit by lia; first [ hyp_by_addr | reflexivity | lia ]
         end.
    unname_sp.
    rename PC into STK. rename PC0 into GUARD. rename PC2 into TDC. clear PC1 POST0.
    lstep. lstep. lstep.
    rewrite bv_eqb_refl. cbv beta iota delta [negb].
    lstep. lstep. lstep.
    lazymatch goal with |- context [if ?c then _ else _] => replace c with false by (vm_compute; reflexivity) end.
    cbv iota.
    lstep. astep.
    lstep. lstep. lstep. lstep. lstep. lstep.
    join2 FRPAD AUXZ. join2 FRPAD FRSAVE.
    release_frame FRPAD STK (bv_unsigned sp).
    apply evt_done. unfold init_libc_post.
    do 17 eexists.
    split; [cbv delta [mkR]; reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: first [ assumption | lia | exact PGC ].
  Qed.
End InitLibc.
