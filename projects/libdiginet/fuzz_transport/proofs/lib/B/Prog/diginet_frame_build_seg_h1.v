(* diginet_frame_build_seg_h1: the image-B run of diginet_frame_build (fuzz_frame.asan-ubsan) from FB_RET_C2
   (0x8276c) to FB_SUM (0x8280c) as a footprint run (lib/Lib/ExecF.v evtF), stepped by lib/Lib/StepF.v: the four
   header stores out+12 := 0x88, out+13 := 0x5f, out+14 := (16 + body_len) >> 8, out+15 := 16 + body_len, each after
   its shadow check; s4 := out + 14 (0x827bc) and s6 := out + 16 (0x82808).
   Each check (`srli` / `add s10` / `lb` / `bnez`) reads the shadow byte of its address; fb_ck_of_addressable gives a
   byte that is 0 (the `bnez` falls through) or above the address mod 8 (the `andi` / `blt` of the slow path at
   0x82af4, 0x82b00, 0x82b0c, 0x82b1c goes back), so no errpath_store1 call is reached. The two paths of a check meet
   again at the instruction after the `bnez`, with one register (a2 for the first two checks, a1 for the third, a3
   for the fourth) set by the slow path only; the proof of the rest of the run is made once, for every value of that
   register.
   The five branches to the `unimp` word at 0x82af0 (`bltu` of -13 and s0 at 0x82770, `beq` of out + 12 and -1 at
   0x82794, `bltu` of -15 and s0 at 0x827b8, `beq` of s4 and -1 at 0x827e4, `bltu` of -3 and s4 at 0x82804) test a
   wrap of out + K; 0 < out and out + the length of the bytes at out <= 2 ^ 63 make each condition false. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof diginet_frame_build_iface.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- the 16 first bytes of the output, as cells ---- *)

Lemma fbh1_split16 : forall (l : list byte) d, (16 <= length l)%nat ->
  l = firstn 12 l ++ [nth 12 l d; nth 13 l d; nth 14 l d; nth 15 l d] ++ skipn 16 l.
Proof.
  intros l d H.
  do 16 (destruct l as [|? l]; [cbn [length] in H; lia|]).
  reflexivity.
Qed.

(* The output as cells: bytes 0 .. 11, the four bytes 12 .. 15 one cell each, then the rest. *)
Lemma fbh1_split : forall m out l, (16 <= length l)%nat ->
  rw_cells rsegs m out [CB (length l) l] ->
  exists pre post (n2 : nat) b12 b13 b14 b15,
    pre = firstn 12 l /\ post = skipn 16 l /\ n2 = (length l - 16)%nat /\
    rw_cells rsegs m out [CB 12 pre; C1 b12; C1 b13; C1 b14; C1 b15; CB n2 post].
Proof.
  intros m out l Hl [[Hwf Hb] Hw].
  set (d := Z_to_bv 8 0).
  exists (firstn 12 l), (skipn 16 l), (length l - 16)%nat, (nth 12 l d), (nth 13 l d), (nth 14 l d), (nth 15 l d).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  pose proof (fbh1_split16 l d Hl) as E. cbn [app] in E.
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn. repeat split; lia.
  - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in Hb |- *. rewrite <- E. exact Hb.
  - cbn [cells_size csize] in *.
    match goal with |- wr_at _ _ _ (Z.of_nat ?n) => replace n with (length l + 0)%nat by lia end.
    exact Hw.
Qed.

(* Back to one cell, with the four bytes written. *)
Lemma fbh1_merge : forall m out l pre post (n2 : nat) x12 x13 x14 x15, (16 <= length l)%nat ->
  pre = firstn 12 l -> post = skipn 16 l -> n2 = (length l - 16)%nat ->
  rw_cells rsegs m out [CB 12 pre; C1 x12; C1 x13; C1 x14; C1 x15; CB n2 post] ->
  rw_cells rsegs m out [CB (length l) (fb_put l 12 [x12; x13; x14; x15])].
Proof.
  intros m out l pre post n2 x12 x13 x14 x15 Hl -> -> -> [[Hwf Hb] Hw].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. apply fb_put_length. cbn [length]. lia.
  - cbn [cells_bytes cbytes app] in *. unfold fb_put. cbn [length app Nat.add].
    rewrite !app_nil_r in Hb |- *. exact Hb.
  - cbn [cells_size csize] in *.
    match goal with |- wr_at _ _ _ (Z.of_nat ?n) =>
      replace n with (12 + (1 + (1 + (1 + (1 + (length l - 16 + 0))))))%nat by lia end.
    exact Hw.
Qed.

(* ---- the shadow range, the stored bytes ---- *)

Lemma fbh1_sh_rng : forall RNG a b x,
  rng RNG (shadow_addr a) (shadow_addr b - shadow_addr a + 1) -> a <= x <= b ->
  rng RNG (shadow_addr x) 1.
Proof.
  intros RNG a b x H Hx. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* transport's Lib/Step.v stores `le1 v` as the cell C1 (Z_to_bv 8 (bv_unsigned v)); this is that byte. *)
Lemma fbh1_c1 : forall (v : word) z, bv_unsigned v mod 2 ^ 8 = z mod 2 ^ 8 -> Z_to_bv 8 (bv_unsigned v) = b8 z.
Proof.
  intros v z H. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H.
Qed.

(* Rename the stored byte C1 (Z_to_bv 8 (bv_unsigned v)) of the cell list to b8 z (tac proves the byte equation). *)
Ltac fbh1_c1h z tac :=
  match goal with
  | H : rw_cells _ _ _ ?cs |- _ =>
      match cs with context [C1 (Z_to_bv 8 (bv_unsigned ?v))] => rewrite (fbh1_c1 v z) in H by tac end
  end.

(* `slli a0,a1,0x30 ; srli a0,a0,0x38`: the second byte of a 16-bit value. *)
Lemma fbh1_hi_byte : forall v, 0 <= v < 2 ^ 16 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl v 48))) 56)) = v / 2 ^ 8.
Proof.
  intros v Hv.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (v * 2 ^ 48)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (v * 2 ^ 48 / 2 ^ 56) with (v / 2 ^ 8).
  2:{ change (2 ^ 56) with (2 ^ 48 * 2 ^ 8). rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity. }
  apply unsigned_lit. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* ---- the tactics of one check ---- *)

Ltac fbh1_lit X := let v := eval vm_compute in X in change X with v.

(* A branch to the `unimp` word at 0x82af0: `bltu` of a literal L and out + K, or `beq` of out + K and -1. The
   premises 0 < out and out + length l <= 2 ^ 63 make the condition false, so the branch falls through. *)
Ltac fbh1_ff HO HL H30 :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [ cbv iota
      | symmetry; unfold c_ltu, bv_ltu, bv_eqb; rewrite ?unsigned_lit_wrap;
        first [ apply Z.ltb_ge | apply Z.eqb_neq ];
        clear - HO HL H30; Z.div_mod_to_equations; lia ]
  end.

(* The shadow byte of X in the current memory mm, from addressable m (out + 12) 4 carried to mm. *)
Ltac fbh1_sh out HAPP AD X k M K :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ ?m0 mm |- _ =>
      destruct (fb_ck_of_addressable mm (out + 12) 4 X 1
                  (fb_addressable_tp m0 mm (out + 12) 4 (out + 12) (out + 16) MU HAPP AD)
                  ltac:(lia) ltac:(lia) ltac:(lia)) as (k & M & K);
      unfold shadow_addr, ASAN_K in M
    end
  end.

(* The two paths of the check meet at B with register r changed: prove the rest once, for every value of r. *)
Ltac fbh1_bj G r :=
  lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R (Z_to_bv 5 r))) end.

Ltac fbh1_chk r X k K :=
  let MB := fresh "MB" in
  pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB;
  lazymatch goal with
  | |- evtF ?segs ?RNG0 ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RNG0 Q (MS (bvmap_set (Z_to_bv 5 r) rr R) F B fc rv mm ro));
      [ rewrite sxb_eq0;
        let C := fresh "C" in
        destruct K as [C | [C _]];
        [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; fbh1_bj G r
        | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
          step; step;
          rewrite land7, (unsigned_lit X) by lia;
          rewrite (lts_low (X mod 8) k MB);
          rewrite (proj2 (Z.ltb_lt (X mod 8) (bv_signed k)) ltac:(lia)); cbn [negb];
          fbh1_bj G r ]
      | let rr := fresh "rr" in intros rr; simp_regs; clear K MB ]
  end.

(* srli d,a,0x3 ; add d,d,s10 ; lb d,0(d) ; bnez d (a = X) *)
Ltac fbh1_check out HAPP AD RS r X :=
  let g := fresh "g" in let Gg := fresh "Gg" in let h := fresh "h" in let Hh := fresh "Hh" in
  let k := fresh "k" in let M := fresh "M" in let K := fresh "K" in let RH := fresh "RH" in
  let R := fresh "R" in
  step; gen_shr (Z_to_bv 64 X) g Gg;
  rewrite (unsigned_lit X) in Gg by lia;
  step; gen_addi g h Hh;
  fbh1_sh out HAPP AD X k M K;
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rdw0 mm h _ _ M ltac:(lia)) as R
  end;
  step; clear R;
  step;
  fbh1_chk r X k K;
  clear M RH Gg Hh.

Lemma fb_h1_F : fb_h1_stmt.
Proof.
  unfold fb_h1_stmt.
  intros RNG ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m out blen l
    HO HL H30 HBL CELLS AD RO RSH.
  fbh1_lit FB_RET_C2. fbh1_lit FB_SUM. unfold ASAN_K.
  assert (HAPP : forall a, out + 12 <= a < out + 16 -> app_mem a).
  { intros a Ha. destruct AD as (_ & _ & _ & HA). destruct (HA (a - (out + 12)) ltac:(lia)) as [Hp _].
    replace (out + 12 + (a - (out + 12))) with a in Hp by lia. exact Hp. }
  pose proof (fbh1_sh_rng RNG (out + 12) (out + 15) (out + 12) RSH ltac:(lia)) as RS12.
  pose proof (fbh1_sh_rng RNG (out + 12) (out + 15) (out + 13) RSH ltac:(lia)) as RS13.
  pose proof (fbh1_sh_rng RNG (out + 12) (out + 15) (out + 14) RSH ltac:(lia)) as RS14.
  pose proof (fbh1_sh_rng RNG (out + 12) (out + 15) (out + 15) RSH ltac:(lia)) as RS15.
  unfold shadow_addr, ASAN_K in RS12, RS13, RS14, RS15. clear RSH.
  destruct (fbh1_split m out l ltac:(lia) CELLS) as (pre & post & n2 & b12 & b13 & b14 & b15 & Epre & Epost & En2 & CH).
  clear CELLS.
  pose proof (munch_refl [(out + 12, out + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x8276c li a0,-13; 0x82770 bltu a0,s0: out <= 2 ^ 64 - 13, not taken *)
  step. step. fbh1_ff HO HL H30.
  (* 0x82774 addi a0,s0,12; the check of out+12 (0x82778 .. 0x82784; slow path 0x82af4 / 0x82af8, a2) *)
  step.
  fbh1_check out HAPP AD RS12 12 (out + 12).
  (* 0x82788 li a1,136; li a2,-1; sb a1,0(a0); 0x82794 beq a0,a2: out + 12 <> 2 ^ 64 - 1 *)
  step. step. step.
  step. fbh1_ff HO HL H30.
  (* 0x82798 addi a0,s0,13; the check of out+13 (0x8279c .. 0x827a8; slow path 0x82b00 / 0x82b04, a2) *)
  step.
  fbh1_check out HAPP AD RS13 12 (out + 13).
  (* 0x827ac li a0,95; li a1,-15; sb a0,13(s0); 0x827b8 bltu a1,s0: out <= 2 ^ 64 - 15 *)
  step. step. step.
  step. fbh1_ff HO HL H30.
  (* 0x827bc addi s4,s0,14; the check of out+14 (0x827c0 .. 0x827cc; slow path 0x82b0c / 0x82b10, a1) *)
  step.
  fbh1_check out HAPP AD RS14 11 (out + 14).
  (* 0x827d0 addi a1,s1,16; slli a0,a1,0x30; srli a0,a0,0x38; li a2,-1; sb a0,0(s4) *)
  step. step. step. step. step.
  fbh1_c1h ((16 + blen) / 2 ^ 8) ltac:(rewrite (unsigned_lit (blen + 16)) by lia;
    rewrite fbh1_hi_byte by lia; replace (blen + 16) with (16 + blen) by lia; reflexivity).
  (* 0x827e4 beq s4,a2: out + 14 <> 2 ^ 64 - 1 *)
  step. fbh1_ff HO HL H30.
  (* 0x827e8 addi a0,s0,15; the check of out+15 (0x827ec .. 0x827f8; slow path 0x82b1c / 0x82b20, a3) *)
  step.
  fbh1_check out HAPP AD RS15 13 (out + 15).
  (* 0x827fc li a0,-3; sb a1,15(s0) *)
  step. step.
  fbh1_c1h (16 + blen) ltac:(rewrite (unsigned_lit (blen + 16)) by lia; f_equal; lia).
  (* 0x82804 bltu a0,s4: out + 14 <= 2 ^ 64 - 3; 0x82808 addi s6,s0,16 *)
  step. fbh1_ff HO HL H30.
  step.
  apply evtF_done.
  do 5 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  pose proof (fbh1_merge _ out l pre post n2 _ _ _ _ ltac:(lia) Epre Epost En2 CH) as CM.
  unfold put16. cbn [app].
  replace (b8 (0x885f / 2 ^ 8)) with (Z_to_bv 8 136) by (apply bv_eq; vm_compute; reflexivity).
  replace (b8 0x885f) with (Z_to_bv 8 95) by (apply bv_eq; vm_compute; reflexivity).
  exact CM.
Qed.
