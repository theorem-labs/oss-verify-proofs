(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_secalloc_math.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc R_secalloc_p2 R_secalloc_p3 R_secalloc_p4 R_secalloc_B0 R_mmapfixed R_mapordie R_secalloc_B1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac hide_disj := repeat match goal with
  | H : (?A \/ ?B) |- _ => change (hide (A \/ B)) in H
  end.
(* [comment removed for export] *)
Ltac lia_p := zify_prune_plain; Zify.zify; xlia zchecker.
Ltac disj_one :=
  first [ lia_p
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; destruct H' as [H'|H']; lia_p
          end ].
Ltac my_disj := repeat match goal with |- _ /\ _ => split end; try exact I; disj_one.
Local Ltac tslia ::= first [ exact I | clear_big; my_disj ].

(* [comment removed for export] *)
Lemma u64s_repeat0 : forall k, u64s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (8 * k).
Proof.
  induction k as [|k IH]; [reflexivity|].
  replace (8 * S k)%nat with (8 + 8 * k)%nat by lia. rewrite repeat_app, <- IH. reflexivity.
Qed.

Lemma u64arr_app_zeros : forall (m : mem) A ws k, (0 <= k)%Z ->
  u64arr asegs m A ws ->
  rw_cells asegs m (A + 8 * Z.of_nat (length ws)) [CB (Z.to_nat (8 * k)) (repeat (Z_to_bv 8 0) (Z.to_nat (8 * k)))] ->
  u64arr asegs m A (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat k)).
Proof.
  intros m A ws k Hk [Hb Hw] [[_ Hz] Hzw].
  assert (E8 : Z.to_nat (8 * k) = (8 * Z.to_nat k)%nat) by lia.
  rewrite E8 in Hz, Hzw. cbn [cells_bytes cbytes] in Hz. rewrite app_nil_r in Hz.
  cbn [cells_size csize] in Hzw. rewrite Nat.add_0_r in Hzw.
  split.
  - rewrite u64s_app, u64s_repeat0. apply bytes_at_app. split; [exact Hb|].
    rewrite u64s_length. replace (A + Z.of_nat (8 * length ws))%Z with (A + 8 * Z.of_nat (length ws))%Z by lia. exact Hz.
  - rewrite app_length, repeat_length.
    replace (8 * Z.of_nat (length ws + Z.to_nat k))%Z with (8 * Z.of_nat (length ws) + Z.of_nat (8 * Z.to_nat k))%Z by lia.
    apply sec_wr_at_app2; [lia| lia|]. split; [exact Hw| exact Hzw].
Qed.

(* [comment removed for export] *)
Definition sb2_W (sp P PAB nres : Z) : list (Z * Z) :=
  ((PAB + 8 * nres, PAB + 8 * nres + 0x20000) :: (sp - 192, sp - 96) :: (i_sec_nres, i_sec_nres + 8) :: sa_W4 PAB nres P)%Z.

Definition sb2_K (P SZ PAB nres T : Z) (ws : list word) (mm md : word) (m : mem) : Prop :=
  shdr m P (sa_msz SZ) SZ nres
  /\ rw_cells asegs m (P + 32) [CB (Z.to_nat (sa_msz SZ - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (sa_msz SZ - 32)))]
  /\ rw_cells asegs m (shad P) [CB 512 (repeat (Z_to_bv 8 250) 512)]
  /\ rw_cells asegs m (shad (P + 4096 + SZ))
       [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)))]
  /\ rw_cells asegs m (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm + 1)); C8 (Z_to_bv 64 (bv_unsigned md + sa_msz SZ))]
  /\ sec_core m PAB (nres + 16384) (nres + 1) /\ sec_pad m /\ sec_junk m
  /\ u64arr asegs m PAB (upd (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat 16384)) (Z.to_nat nres) (Z_to_bv 64 P)).

Lemma secalloc_B2_spec : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (mB : mem) (SZ P PAB nres T lo k : Z) (ws : list word) (mm md : word),
  (65536 < SZ /\ SZ mod 8 = 0 /\ SZ + 16384 <= 2^47)%Z -> (P mod 4096 = 0)%Z -> (PAB mod 4096 = 0)%Z ->
  gobj P (sa_msz SZ) lo -> gobj T 4096 lo -> gobj PAB 0x800000 lo ->
  sapart P (sa_msz SZ) T 4096 -> sapart P (sa_msz SZ) PAB 0x800000 -> sapart T 4096 PAB 0x800000 ->
  Z.of_nat (length ws) = nres -> (0 <= nres)%Z -> (nres + 16384 <= 2^20)%Z -> (nres mod 16384 = 0)%Z ->
  (0 <= k < 64)%Z -> (2 ^ k <= sa_msz SZ < 2 ^ (k + 1))%Z ->
  mfi_frame mB (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 0x19fc00) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
    (Z_to_bv 64 (sa_msz SZ)) (Z_to_bv 64 (63 - k)) (Z_to_bv 64 (P + 4096)) ->
  stk asegs mB lo (bv_unsigned sp - 192) -> mm_gcells mB ->
  sb1_mid sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 P SZ PAB nres T ws mm md mB ->
  (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 464)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs mB ->
  evt asegs (secalloc_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (sb2_W (bv_unsigned sp) P PAB nres) (P + 4096) lo mB (sb2_K P SZ PAB nres T ws mm md))
    (nret (MSsvc (mfi0_regs (Z_to_bv 64 0x19fc00) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6
                   (PAB + 8 * nres) 0x20000 (Z_to_bv 64 P) (Z_to_bv 64 (P + sa_msz SZ)) (Z_to_bv 64 (P + 4096 + SZ))
                   (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096)) s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None mB (seg_rom asegs))
          (mkEffect (Z_to_bv 64 (PAB + 8 * nres)) [] [(Z_to_bv 64 (PAB + 8 * nres), Z_to_bv 64 0x20000)])).
Proof.
  intros until md. intros HSZ HP HPAB GP GT GA APT APA ATA Hlen Hn0 Hnres Hnres16 Hk Hx MF ST MM MID HLOH HLO HSP MI.
  destruct MID as (jf & b & jj & w1 & w2 & w3 & w4 & ga & gm & bl & FR & CH & NR & SJ1 & Hbl & SJ2 & SJ3 & LW & ARR & SRG & HD3 & HI
                   & RMP & SH1 & SH2 & TS).
  pose proof (sa_msz_facts SZ ltac:(lia)) as [MS1 MS2].
  pose proof GP as GP0. pose proof GA as GA0. pose proof APA as APA0. apply box in GP0, GA0, APA0.
  destruct GP as (GP1 & GP2 & GP3 & GP4). destruct GT as (GT1 & GT2 & GT3 & GT4). destruct GA as (GA1 & GA2 & GA3 & GA4).
  unfold sapart, img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  assert (GP4' : (12345344 <= P)%Z) by (destruct GP4; lia). clear GP4.
  assert (GA4' : (12345344 <= PAB)%Z) by (destruct GA4; lia). clear GA4.
  pose proof (sa_shad_facts P SZ lo HP ltac:(lia) ltac:(lia) (unbox _ GP0) ltac:(lia)) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8 & SRc).
  rewrite SR7 in SH2. apply box in SR7.
  set (z8 := (SZ / 8)%Z) in *. set (ms8 := (sa_msz SZ / 8)%Z) in *. clearbody z8 ms8.
  assert (MS8 : (8704 <= ms8)%Z) by lia.
  pose proof HSZ as (HSZ1 & HSZ2 & HSZ3).
  assert (HL8 : (8 * nres + 0x20000 <= 0x800000)%Z) by lia.
  assert (HNA : (PAB + 8 * nres) mod 4096 = 0%Z) by (Z.div_mod_to_equations; lia).
  apply box in HP, MS2, HSZ2, Hnres16, HSZ, HPAB, HNA.
  change i_sec_chunks with 6722848%Z in CH. change i_sec_nres with 6722888%Z in NR. change i_sec_mutex with 6723456%Z in LW.
  change i_sec_sorted with 6722904%Z in SJ1. change i_sec_bylog with 6722944%Z in SJ2. change i_gstat_alloc with 6723480%Z in SJ3.
  unfold sec_range, i_sec_range in SRG. change (INST + 0x50)%Z with 6722856%Z in SRG.
  pose proof MM as (G1 & G2 & G3 & G4 & G5). clear MM.
  pose proof (munch_refl (sb2_W (bv_unsigned sp) P PAB nres) mB) as MU. unfold sb2_W, sa_W4 in MU.
  change i_sec_nres with 6722888%Z in MU. change i_sec_sorted with 6722904%Z in MU. change i_sec_bylog with 6722944%Z in MU.
  change i_gstat_alloc with 6723480%Z in MU. change i_sec_mutex with 6723456%Z in MU.
  pose proof (wmono_refl asegs mB) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) = (bv_unsigned sp - 96)%Z) by (apply unsigned_lit; lia).
  hide_disj.
  eapply evt_cut; [eapply (mfi0_B_spec (Z_to_bv 64 0x19fc00) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA)
      t0 t1 t2 a6 (Z_to_bv 64 P) (Z_to_bv 64 (P + sa_msz SZ)) (Z_to_bv 64 (P + 4096 + SZ)) (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096))
      s10 s11 t3 t4 t5 t6 F fc mB (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC) (Z_to_bv 64 (sa_msz SZ)) (Z_to_bv 64 (63 - k))
      (Z_to_bv 64 (P + 4096)) (PAB + 8 * nres) 0x20000 lo) | post_call asegs mB].
  all: rewrite ?ESP.
  1-3: lia.
  1:{ unfold hide, img_hull_lo, img_hull_hi. right. lia. }
  1:{ exact MF. }
  1:{ unfold mm_gcells. repeat (split; [assumption|]). assumption. }
  1:{ replace (bv_unsigned sp - 96 - 96)%Z with (bv_unsigned sp - 192)%Z by lia. exact ST. }
  1:{ unfold kHighShadowEnd. lia. }
  1-2: lia.
  1:{ exact MI. }
  change SEC with 6722840%Z. change GSTAT with 6723464%Z.
  rewrite <- Hlen in PC. change (Z.to_nat 131072) with (Z.to_nat (8 * 16384)) in PC.
  pose proof (u64arr_app_zeros _ PAB ws 16384 ltac:(lia) ARR PC) as ARRx. clear ARR PC.
  rewrite ESP in PC0.
  zhide.
  do 7 zstep.
  eapply evt_mono.
  1:{ eapply (sa_p4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 jf _ P SZ PAB (nres + 16384) nres
        k lo (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat 16384))).
      1:{ lia. }
      1:{ exact (unbox _ HP). }
      1:{ exact Hk. }
      1:{ exact (unbox _ GP0). }
      1:{ rewrite app_length, repeat_length. destruct (unbox _ GA0) as (? & ? & ? & ?). split; [lia|]. split; [lia|]. split; lia. }
      1:{ rewrite app_length, repeat_length. destruct (unbox _ APA0); [left; lia| right; lia]. }
      1:{ rewrite app_length, repeat_length. lia. }
      1:{ rewrite ESP. exact FR. }
      1:{ rewrite ESP. exact PC0. }
      1:{ unfold kHighShadowEnd. lia. }
      1:{ rewrite ESP. lia. }
      1:{ rewrite ESP. lia. }
      1:{ exact CH. }
      1:{ exact NR. }
      1:{ unfold sec_junk. split; [do 6 eexists; exact SJ1|]. split; [eexists; split; [exact Hbl| exact SJ2]|].
          do 2 eexists; exact SJ3. }
      1:{ exact LW. }
      1:{ exact ARRx. }
      1:{ exact HI. }
      1:{ assumption. } }
  intros ms' PO.
  rewrite ESP in PO. replace (bv_unsigned sp - 96 + 96)%Z with (bv_unsigned sp) in PO by lia. rewrite Z_to_bv_bv_unsigned in PO.
  unfold secalloc_post in PO.
  destruct PO as (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m3 & E & MU4 & WM4 & MI4 & ST4
                  & (HI' & ARR' & NR' & SJ' & MX' & PAD')).
  subst ms'.
  clear FR PC0 NR SJ1 SJ2 SJ3 LW ARRx HI G1 G2 G3 G4 G5 POST SRG.
  unfold sa_W4 in MU4.
  change i_sec_nres with 6722888%Z in MU4. change i_sec_sorted with 6722904%Z in MU4. change i_sec_bylog with 6722944%Z in MU4.
  change i_gstat_alloc with 6723480%Z in MU4. change i_sec_mutex with 6723456%Z in MU4.
  lazymatch type of MU4 with munch _ ?mm _ => transport_after_call asegs mm m3 MU4 WM4 end. clear MU4 WM4.
  unfold secalloc_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact ST4|].
  unfold sb2_K. split.
  - unfold shdr.
    apply (sec_rw_app2 _ P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)] [C8 (Z_to_bv 64 nres)]).
    split; [exact HD3| exact HI'].
  - split; [exact RMP|]. split; [exact SH1|]. split; [rewrite (unbox _ SR7); exact SH2|]. split; [exact TS|].
    split; [split; [exact CH| split; [exact NR'| exact MX']]|]. split; [exact PAD'|]. split; [exact SJ'| exact ARR'].
Qed.
