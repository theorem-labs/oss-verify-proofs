(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0StrlenIcpt_b Ba0TlsGetAddr_b Ba0FakeStack1_b Ba0FakeStackGC_b Ba0Fsm3Core_b Ba0Fsm3Gen_b Ba0FakeStackGCC_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r48448_48dd8_b Ba0_code_r4dae8_4daec_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation CLS := 3%Z.                  (* [comment removed for export] *)

Section FPX_1. Context {fx : PropExec.FPState}.


#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].


#[local] Ltac wv2 := gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  try change (2 ^ 7)%Z with 128%Z; first [reflexivity | f_equal; lia].

#[local] Ltac kbt := first [ solve [repeat first [left; reflexivity | right]]
                           | let HIn := fresh "HIn" in let E := fresh "E" in intros HIn; repeat (destruct HIn as [E|HIn]; [discriminate E|]); exact HIn ].
#[local] Ltac pw e := let v := eval vm_compute in e in change e with v.
#[local] Ltac pwin e H := let v := eval vm_compute in e in change e with v in H.

Section GCC3.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra a0v : word.
  (* [comment removed for export] *)
  Variables s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
  (* [comment removed for export] *)
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 208)%Z /\ (s < 2 ^ 64)%Z.          (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 208)) 208%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hmd : (0 <= md < 255)%Z.
  Hypothesis Hoff : (0 <= off < 2 ^ 64)%Z.
  Hypothesis Hdtv : (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z.
  Hypothesis Hent : (0 <= ent < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 64 <= 2 ^ 64)%Z.
  Hypothesis Htbe : (0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z.
  Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
  Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
  Hypothesis Hverb : (0 <= verb < 3)%Z.
  Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
  Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
  Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
  Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
    tls_cells tpv 0x1382b8 md off dtv ent key tsd ctx th tb te F V verb dto blk rec M'.

  Variable fs : Z.
  Hypothesis Hfs0 : (0 < fs < 2 ^ 64)%Z.
  Hypothesis Hr : (0 <= tls_rp off ent /\ tls_rp off ent + 8 < 2 ^ 64)%Z /\ (tls_rp off ent + 8 <= s - 208 \/ s <= tls_rp off ent)%Z.
  Hypothesis HRfs : rdn ASEGS mem0 (Z_to_bv 64 (tls_rp off ent)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).

  Variables h j pos ff : Z.
  Variables top botth g40 g35 : Z.
  Variables flag rs : Z -> Z -> Z.                 (* [comment removed for export] *)
  #[local] Abbreviation col := (gc_col s botth flag rs).
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Happm : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.      (* [comment removed for export] *)
  Hypothesis Hshz : (gc_shz_hi fs <= s - 208 \/ s <= gc_shz_lo fs)%Z.                                 (* [comment removed for export] *)
  Hypothesis Hh : (0 <= h < 2 ^ 64)%Z.
  Hypothesis Hj : (0 <= j < 2048)%Z.
  Hypothesis Hpos_def : pos = ((h + j) mod 2048)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 3145728 + 512 * pos)%Z.
  Hypothesis Hng : rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 1].                      (* [comment removed for export] *)
  Hypothesis Hssl : rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).
  Hypothesis Hhint : rdn ASEGS mem0 (Z_to_bv 64 (fs + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)).
  Hypothesis HF0 : forall c i, gc_valid c i ->
    rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z.
  (* [comment removed for export] *)
  Hypothesis Hprobe : forall i, (0 <= i < j)%Z -> flag CLS ((h + i) mod 2048) <> 0%Z /\ ~ col CLS ((h + i) mod 2048).
  Hypothesis Hflag : flag CLS pos = 0%Z \/ col CLS pos.
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis Hshadow_ok : store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) 64%nat = true.
  Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (botth <= s <= top)%Z.   (* [comment removed for export] *)
  Hypothesis Hth80 : (th + 80 <= 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis HCG : forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
     rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
     rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\
     rdn ASEGS M' (0x1374b8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
     rdn ASEGS M' (0x10380 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35)).
  (* [comment removed for export] *)
  Hypothesis HRS : forall M', (forall x : word, gc_outz (s - 208) s fs (bv_unsigned x) -> M' x = mem0 x) ->
     forall c i, gc_valid c i -> flag c i <> 0%Z ->
       rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z.
  Hypothesis Hcol6 : forall c i, gc_valid c i -> col c i -> (c <= 6)%Z.
  Hypothesis Hshok : forall c i, gc_valid c i -> col c i -> store_ok ASEGS mem0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true.

  #[using="md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 Hfs0 Hr HRfs top g40 g35 Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok"] Theorem fsm3_gcc_run : forall regs,
    getr regs 10 = a0v -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mg,
      msteps ASEGS (mkst regs (0x5df30 : word) mem0 rom) (mkst regs' ra (core3_mem Mg s fs h j pos ff) rom)
      /\ getr regs' 10 = Z_to_bv 64 ff /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ gc_post mem0 Mg (s - 208) s fs col.
  Proof.
    intros regs H10 H4 H2 H1.
    assert (SPS : sp = Z_to_bv 64 s) by (rewrite <- Hs_def; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (fsm3_pre_run mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx
                Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs regs H10 H4 H2 H1) as (r2 & M2 & RUNP & P9 & P8 & P2 & KP & O2 & G2 & SLOTS).
    destruct Hfs as (Fs1 & Fs2 & Fs3). destruct Hs as [Sa Sb]. destruct Htop as (Tp1 & Tp2 & Tp3 & Tp4).
    pose proof (gc_shz_facts fs Fs1 Fs3 Happm) as (Z1 & Z2 & Z3 & Z4).
    pose proof (Z.mod_pos_bound (h + j) 2048 ltac:(lia)) as Hposb. rewrite <- Hpos_def in Hposb.
    assert (Vpos : gc_valid CLS pos) by (split; [lia | pw (2 ^ (14 - CLS))%Z; lia]).
    assert (Eff : gc_fr fs CLS pos = ff) by (unfold gc_fr; pw (2 ^ (6 + CLS))%Z; rewrite Hff_def; lia).
    assert (Esh : gc_sh fs CLS pos = (SB + ff / 8)%Z) by (unfold gc_sh; rewrite Eff; reflexivity).
    assert (Efl : forall p, gc_fl fs CLS p = (fs + 4096 + 28672 + p)%Z) by (intros p; unfold gc_fl; pw (2 ^ (14 - CLS))%Z; lia).
    pose proof (gc_sh_range fs CLS pos Vpos) as [SHR1 SHR2]. rewrite Esh in SHR1, SHR2. pwin (2 ^ (3 + CLS))%Z SHR2.
    assert (EQ : forall (a : Z) (k : nat), (0 <= a)%Z -> (a + Z.of_nat k < 2 ^ 64)%Z -> (a + Z.of_nat k <= s - 208 \/ s <= a)%Z ->
                 rdn ASEGS M2 (Z_to_bv 64 a) k = rdn ASEGS mem0 (Z_to_bv 64 a) k).
    { intros a k Ha Hk1 Hk2. apply rdn_ext; [unorm; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply O2. lia. }
    pose proof Hng as C1. rewrite <- (EQ (fs + 96)%Z 1%nat) in C1 by (cbn [Z.of_nat Pos.to_nat]; lia).
    pose proof Hssl as C2. rewrite <- (EQ (fs + 88)%Z 8%nat) in C2 by (cbn [Z.of_nat Pos.to_nat]; lia).
    assert (T4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (KP 4%bv) by kbt; exact H4).
    (* [comment removed for export] *)
    assert (S3a : exists r3a, msteps ASEGS (mkst r2 (0x5df5c : word) M2 rom) (mkst r3a (0x5d7e0 : word) M2 rom)
              /\ (getr r3a 10 = Z_to_bv 64 fs /\ getr r3a 11 = Z_to_bv 64 s /\ getr r3a 18 = Z_to_bv 64 20 /\ getr r3a 9 = Z_to_bv 64 fs /\ getr r3a 8 = Z_to_bv 64 s
                  /\ getr r3a 4 = Z_to_bv 64 tpv /\ getr r3a 2 = Z_to_bv 64 (s - 32) /\ getr r3a 1 = (0x5df74 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3a)).
    { eexists. split.
      - chain_step; [reflexivity | eapply step_lbu; [exact F_5db44 | reflexivity | exact D_5db44
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 96)) by (symmetry; wv2) end; exact C1] | step_simpl; vnorm].   (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_5db48 | reflexivity | exact D_5db48
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 88)) by (symmetry; wv2) end; exact C2 | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb F_5db4c D_5db4c.                                                                             (* [comment removed for export] *)
        stepiv F_5db50 D_5db50 (Z_to_bv 64 fs) ltac:(wv2).                                                (* [comment removed for export] *)
        stepiv F_5db54 D_5db54 (Z_to_bv 64 s) ltac:(wv2).                                                 (* [comment removed for export] *)
        stepn F_5db58 D_5db58.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (match goal with |- ?g => check_closed_term g; apply bv_eq; vm_compute; reflexivity end). solve_keeps_but. }
    destruct S3a as (r3a & RUN3a & X10 & X11 & X18 & X9 & X8 & X4 & X2 & X1 & K3a).
    (* [comment removed for export] *)
    assert (Hrg : ret_ok (0x5df74 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (OkG : store_ok ASEGS M2 (Z_to_bv 64 (s - 32 - 160)) 160%nat = true).
    { apply (store_ok_mono _ _ mem0 M2 _ G2). apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]. }
    assert (HF2 : forall c i, gc_valid c i -> rdn ASEGS M2 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z).
    { intros c i Vc. destruct (HF0 c i Vc) as [R B]. split; [|exact B]. pose proof (gc_fl_range fs c i Vc) as FR.
      rewrite (EQ (gc_fl fs c i) 1%nat) by (cbn [Z.of_nat Pos.to_nat]; lia). exact R. }
    assert (HCT2 : forall M', (forall x : word, (bv_unsigned x < s - 32 - 160 \/ s - 32 <= bv_unsigned x)%Z -> M' x = M2 x) ->
       rdn ASEGS M' (0x13f4a0 : word) 1%nat = Some [Z_to_bv 8 1] /\
       rdn ASEGS M' (0x13f4a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
       rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
       rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
       rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
       rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
       rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
       rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\
       rdn ASEGS M' (0x1374b8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
       rdn ASEGS M' (0x10380 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35))).
    { intros M' HM'.
      assert (O' : forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) by (intros x Hx; rewrite (HM' x) by lia; apply O2; exact Hx).
      pose proof (HC0 M' O') as TC. unfold tls_cells in TC.
      destruct TC as (_ & _ & _ & _ & _ & _ & W7 & W8 & W9 & W10 & W11 & _).
      destruct (HCG M' O') as (Q1 & Q2 & Q3 & Q4 & Q5).
      exact (conj W7 (conj W8 (conj W9 (conj W10 (conj W11 (conj Q1 (conj Q2 (conj Q3 (conj Q4 Q5))))))))). }
    assert (HCL2 : forall M', (forall x : word, gc_outz (s - 32 - 160) (s - 32) fs (bv_unsigned x) -> M' x = M2 x) ->
       rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
       /\ rt_layout_globs M'
       /\ (forall c i, gc_valid c i -> flag c i <> 0%Z ->
            rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z)).
    { intros M' HM'.
      assert (O'' : forall x : word, gc_outz (s - 208) s fs (bv_unsigned x) -> M' x = mem0 x).
      { intros x (A1 & A2 & A3). rewrite (HM' x) by (split; [lia | split; assumption]). apply O2. exact A1. }
      assert (EQ'' : forall (a : Z) (k : nat), (0 <= a)%Z -> (a + Z.of_nat k < 2 ^ 64)%Z -> (a + Z.of_nat k <= s - 208 \/ s <= a)%Z ->
                 (a + Z.of_nat k <= fs + 4096 \/ fs + 4096 + 32768 <= a)%Z -> (a + Z.of_nat k <= gc_shz_lo fs \/ gc_shz_hi fs <= a)%Z ->
                 rdn ASEGS M' (Z_to_bv 64 a) k = rdn ASEGS mem0 (Z_to_bv 64 a) k).
      { intros a k Ha Hk1 Hk2 Hk3 Hk4. apply rdn_ext; [unorm; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply O''. unfold gc_outz. (clear - Fs1 Fs2 Happm Hff_def Hfs Hh Hj Hk2 Hk3 Hk4 Hpos_def Hposb Hshz Hx SHR1 SHR2 Sa Z1 Z2 Z3 a ff fs h j k pos s x; lia). }
      split; [rewrite (EQ'' (fs + 88)%Z 8%nat) by (cbn [Z.of_nat Pos.to_nat]; lia); exact Hssl|]. split; [|exact (HRS M' O'')].
      destruct HG as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8). unfold rt_layout_globs.
      rewrite !(rdn_ext ASEGS _ M' mem0) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; lia
        | intros x Hx; apply O''; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; unfold gc_outz; (clear - Fs1 Hx Sa Z2 fs s x; lia)]).
      repeat split; assumption. }
    destruct (gc_collect_run M2 rom (Z_to_bv 64 (s - 32)) (0x5df74 : word) (s - 32) fs s tpv key tsd ctx th top botth g40 g35 flag rs
                ltac:(unorm; reflexivity) Hrg ltac:(lia) OkG Htp Hkey Htsd Hctx ltac:(lia) ltac:(lia) ltac:(lia) Happm ltac:(lia)
                ltac:(apply (store_ok_mono _ _ mem0 M2 _ G2); exact Hwfs) HF2 HCT2 HCL2 Hcol6
                ltac:(intros c i Vc Cc; apply (store_ok_mono _ _ mem0 M2 _ G2); exact (Hshok c i Vc Cc)) r3a X10 X11 X4 X2 X1)
      as (r3b & Mg & RUNG & Y2 & Y1 & KG & GP2).
    assert (GP : gc_post mem0 Mg (s - 208) s fs col) by (apply (gc_post_widen 0 mem0 M2 Mg (s - 208) s (s - 32 - 160) (s - 32) fs col GP2); [lia | lia | exact G2 | exact O2]).
    pose proof GP as (GG & _).
    assert (EQG : forall (a : Z) (k : nat), (0 <= a)%Z -> (a + Z.of_nat k < 2 ^ 64)%Z -> (a + Z.of_nat k <= s - 208 \/ s <= a)%Z -> (a + Z.of_nat k <= fs + 96 \/ fs + 97 <= a)%Z ->
                 (a + Z.of_nat k <= fs + 4096 \/ fs + 4096 + 32768 <= a)%Z -> (a + Z.of_nat k <= gc_shz_lo fs \/ gc_shz_hi fs <= a)%Z ->
                 rdn ASEGS Mg (Z_to_bv 64 a) k = rdn ASEGS mem0 (Z_to_bv 64 a) k).
    { intros a k A1 A2 A3 A4 A5 A6. apply (gc_post_rdn 0 mem0 Mg (s - 208) s fs col a k GP); lia. }
    (* [comment removed for export] *)
    pose proof Hhint as C3g. rewrite <- (EQG (fs + 24)%Z 8%nat) in C3g by (cbn [Z.of_nat Pos.to_nat]; lia).
    assert (CPg : forall i, (0 <= i < j)%Z -> exists b, rdn ASEGS Mg (Z_to_bv 64 (fs + 4096 + 28672 + (h + i) mod 2048)) 1%nat = Some [Z_to_bv 8 b] /\ (0 < b < 256)%Z).
    { intros i Hi. destruct (Hprobe i Hi) as [NZ NC]. pose proof (Z.mod_pos_bound (h + i) 2048 ltac:(lia)) as Pb.
      assert (Vp : gc_valid CLS ((h + i) mod 2048)) by (split; [lia | pw (2 ^ (14 - CLS))%Z; lia]).
      destruct (HF0 CLS ((h + i) mod 2048) Vp) as [R B]. exists (flag CLS ((h + i) mod 2048)). split; [|lia].
      rewrite <- Efl, <- R. apply (gc_post_flag_keep 0 mem0 Mg (s - 208) s fs col CLS _ GP); [lia | lia | lia | lia | exact Vp | exact NC]. }
    assert (C4g : rdn ASEGS Mg (Z_to_bv 64 (fs + 4096 + 28672 + pos)) 1%nat = Some [Z_to_bv 8 0]).
    { rewrite <- Efl. destruct Hflag as [F0|CO].
      - destruct (HF0 CLS pos Vpos) as [R B]. rewrite F0 in R. rewrite <- R.
        apply (gc_post_flag_keep 0 mem0 Mg (s - 208) s fs col CLS pos GP); [lia | lia | lia | lia | exact Vpos |]. intros (NZ & _). contradiction.
      - apply (gc_post_flag_col 0 mem0 Mg (s - 208) s fs col CLS pos GP); [lia | lia | exact Vpos | exact CO]. }
    assert (GLg : rt_layout_globs Mg).
    { destruct HG as (Y1' & Y2' & Y3 & Y4 & Y5 & Y6 & Y7 & Y8). unfold rt_layout_globs.
      rewrite !(rdn_ext ASEGS _ Mg mem0) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; lia
        | intros x Hx; destruct GP as (_ & GPO & _); apply GPO;
          [revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; (clear - Hx Sa s x; lia) | revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; (clear - Fs1 Hx fs x; lia)
          | intros c' i' V' _; pose proof (gc_fl_range fs c' i' V'); pose proof (gc_sh_range fs c' i' V') as [? ?]; unfold gc_insh;
            revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; (clear - Fs1 H H0 Hx Z2 c' fs i' x; lia)]]).
      repeat split; assumption. }
    assert (SLg : rdn ASEGS Mg (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\ rdn ASEGS Mg (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))
               /\ rdn ASEGS Mg (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9)) /\ rdn ASEGS Mg (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))).
    { destruct SLOTS as (SL8 & SL16 & SL24 & SL32).
      rewrite <- (gc_post_rdn 0 M2 Mg (s - 32 - 160) (s - 32) fs col (s - 8) 8 GP2) in SL8 by (cbn [Z.of_nat Pos.to_nat]; lia).
      rewrite <- (gc_post_rdn 0 M2 Mg (s - 32 - 160) (s - 32) fs col (s - 16) 8 GP2) in SL16 by (cbn [Z.of_nat Pos.to_nat]; lia).
      rewrite <- (gc_post_rdn 0 M2 Mg (s - 32 - 160) (s - 32) fs col (s - 24) 8 GP2) in SL24 by (cbn [Z.of_nat Pos.to_nat]; lia).
      rewrite <- (gc_post_rdn 0 M2 Mg (s - 32 - 160) (s - 32) fs col (s - 32) 8 GP2) in SL32 by (cbn [Z.of_nat Pos.to_nat]; lia).
      repeat split; assumption. }
    assert (Z9 : getr r3b 9 = Z_to_bv 64 fs) by (rewrite (KG 9%bv) by kbt; exact X9).
    assert (Z8 : getr r3b 8 = Z_to_bv 64 s) by (rewrite (KG 8%bv) by kbt; exact X8).
    assert (Z18 : getr r3b 18 = Z_to_bv 64 20) by (rewrite (KG 18%bv) by kbt; exact X18).
    assert (INAPP : in_app ff) by (rewrite <- Eff; apply gc_fr_in_app; assumption).
    destruct (@fsm3_core_run fx Mg rom s fs h j pos ff ra (getr regs 8) (getr regs 9) (getr regs 18) Hret ltac:(lia) ltac:(lia) Hh Hj Hpos_def Hff_def C3g CPg C4g
                ltac:(apply (store_ok_mono _ _ mem0 Mg _ GG); exact Hwfs) GLg INAPP ltac:(apply (store_ok_mono _ _ mem0 Mg _ GG); exact Hshadow_ok) ltac:(lia)
                SLg r3b Z9 Z18 Z8 Y2) as (r4 & RUN4 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & K4).
    exists r4, Mg. split; [eapply msteps_trans; [exact RUNP|]; eapply msteps_trans; [exact RUN3a|]; eapply msteps_trans; [exact RUNG | exact RUN4]|].
    split; [exact Q10|]. split; [rewrite Q2; symmetry; exact SPS|]. split; [exact Q1|]. split; [|exact GP].
    assert (KB : keeps_but [1; 2; 8; 9; 18]%bv regs r4).
    { eapply keeps_but_trans; [exact KP|]. eapply keeps_but_trans; [exact K3a|]. eapply keeps_but_trans; [apply keeps_but_cs; exact KG | exact K4]. }
    intros r Hcs. destruct (decide (r = 1%bv)) as [->|N1']; [rewrite Q1, H1; reflexivity|].
    destruct (decide (r = 2%bv)) as [->|N2']; [rewrite Q2, H2; symmetry; exact SPS|].
    destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
    destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|].
    apply KB; [exact Hcs|]. clear -N1' N2' N8 N9 N18. cbv. intuition congruence.
  Qed.
End GCC3.
End FPX_1.
