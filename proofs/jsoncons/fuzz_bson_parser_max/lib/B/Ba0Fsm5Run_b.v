(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0StrlenIcpt_b Ba0TlsGetAddr_b Ba0FakeStack1_b Ba0FakeStackGC_b Ba0Fsm5Core_b Ba0Fsm5Gen_b Ba0FakeStackGCC_b Ba0Fsm5Gcc_b Ba0Fsm5Gce_b Ba0Fsm5Post_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r48448_48dd8_b Ba0_code_5dc38_5de44_b Ba0_code_r4dae8_4daec_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation CLS := 5%Z.                  (* [comment removed for export] *)

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

#[local] Ltac pw e := let v := eval vm_compute in e in change e with v.
#[local] Ltac pwin e H := let v := eval vm_compute in e in change e with v in H.

Section RUN5.
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
  Variable gcb : bool.                             (* [comment removed for export] *)
  Definition fsm5_colg (c i : Z) : Prop := gcb = true /\ (s <= top)%Z /\ gc_col s botth flag rs c i.   (* [comment removed for export] *)
  #[local] Abbreviation col := fsm5_colg.
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Happm : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.      (* [comment removed for export] *)
  Hypothesis Hshz : (gc_shz_hi fs <= s - 208 \/ s <= gc_shz_lo fs)%Z.                                 (* [comment removed for export] *)
  Hypothesis Hh : (0 <= h < 2 ^ 64)%Z.
  Hypothesis Hj : (0 <= j < 512)%Z.
  Hypothesis Hpos_def : pos = ((h + j) mod 512)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 5242880 + 2048 * pos)%Z.
  Hypothesis Hng : rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 (if gcb then 1 else 0)].   (* [comment removed for export] *)
  Hypothesis Hssl : rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).
  Hypothesis Hhint : rdn ASEGS mem0 (Z_to_bv 64 (fs + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)).
  Hypothesis HF0 : forall c i, gc_valid c i ->
    rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z.
  (* [comment removed for export] *)
  Hypothesis Hprobe : forall i, (0 <= i < j)%Z -> flag CLS ((h + i) mod 512) <> 0%Z /\ ~ col CLS ((h + i) mod 512).
  Hypothesis Hflag : flag CLS pos = 0%Z \/ col CLS pos.
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis Hshadow_ok : store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) 256%nat = true.
  (* [comment removed for export] *)
  Hypothesis Htop : gcb = true -> (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (botth <= s)%Z.        (* [comment removed for export] *)
  Hypothesis Hth80 : gcb = true -> (th + 80 <= 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis HCG : gcb = true -> forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
     rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
     rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\
     rdn ASEGS M' (0x1374b8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
     rdn ASEGS M' (0x10380 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35)).
  (* [comment removed for export] *)
  Hypothesis HRS : gcb = true -> forall M', (forall x : word, gc_outz (s - 208) s fs (bv_unsigned x) -> M' x = mem0 x) ->
     forall c i, gc_valid c i -> flag c i <> 0%Z ->
       rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z.
  Hypothesis Hcol6 : forall c i, gc_valid c i -> col c i -> (c <= 6)%Z.
  Hypothesis Hshok : forall c i, gc_valid c i -> col c i -> store_ok ASEGS mem0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true.


  Theorem fsm5_run_any : forall regs,
    getr regs 10 = a0v -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mf,
      msteps ASEGS (mkst regs (0x5e0dc : word) mem0 rom) (mkst regs' ra Mf rom)
      /\ getr regs' 10 = Z_to_bv 64 ff /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ fsm5_post (if (gcb && (top <? s)%Z)%bool then 1 else 0) mem0 Mf (s - 208) s s fs h j pos ff col.
  Proof.
    intros regs H10 H4 H2 H1.
    pose proof Hfs as (Fs1 & Fs2 & Fs3). pose proof Hs as [Sa Sb].
    pose proof (gc_shz_facts fs Fs1 Fs3 Happm) as (Z1 & Z2 & Z3 & Z4).
    pose proof (Z.mod_pos_bound (h + j) 512 ltac:(lia)) as Hposb. rewrite <- Hpos_def in Hposb.
    assert (Vpos : gc_valid CLS pos) by (split; [lia | pw (2 ^ (14 - CLS))%Z; lia]).
    assert (Eff : gc_fr fs CLS pos = ff) by (unfold gc_fr; pw (2 ^ (6 + CLS))%Z; rewrite Hff_def; lia).
    assert (Efl : forall p, gc_fl fs CLS p = (fs + 4096 + 31744 + p)%Z) by (intros p; unfold gc_fl; pw (2 ^ (14 - CLS))%Z; lia).
    pose proof (gc_sh_range fs CLS pos Vpos) as [SHR1 SHR2]. unfold gc_sh in SHR1, SHR2. rewrite Eff in SHR1, SHR2. pwin (2 ^ (3 + CLS))%Z SHR2.
    assert (INAPP : in_app ff) by (rewrite <- Eff; apply gc_fr_in_app; assumption).
    (* [comment removed for export] *)
    assert (NOSCAN : (forall c i, ~ col c i) ->
              (forall i, (0 <= i < j)%Z -> exists b, rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 31744 + (h + i) mod 512)) 1%nat = Some [Z_to_bv 8 b] /\ (0 < b < 256)%Z)
              /\ rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 31744 + pos)) 1%nat = Some [Z_to_bv 8 0]).
    { intros NC. split.
      - intros i Hi. destruct (Hprobe i Hi) as [NZ _]. pose proof (Z.mod_pos_bound (h + i) 512 ltac:(lia)) as Pb.
        assert (Vp : gc_valid CLS ((h + i) mod 512)) by (split; [lia | pw (2 ^ (14 - CLS))%Z; lia]).
        destruct (HF0 CLS ((h + i) mod 512) Vp) as [R B]. exists (flag CLS ((h + i) mod 512)). rewrite <- Efl. split; [exact R | lia].
      - destruct Hflag as [F0|CO]; [|destruct (NC _ _ CO)]. destruct (HF0 CLS pos Vpos) as [R _]. rewrite F0, Efl in R. exact R. }
    pose proof Hng as Hng'. destruct gcb eqn:EG; [destruct (Z.ltb_spec top s) as [EARLY|SCAN]|]; cbn [andb].
    - (* [comment removed for export] *)
      assert (NC : forall c i, ~ col c i) by (intros c i (_ & X & _); lia).
      destruct (NOSCAN NC) as [CP C4]. destruct (Htop eq_refl) as (Tp1 & Tp2 & Tp3 & Tp4).
      destruct (fsm5_gce_run mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd
                  Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth Hfs Hh Hj Hpos_def Hff_def Hng' Hssl Hhint CP C4 Hwfs HG INAPP Hshadow_ok
                  ltac:(lia) ltac:(lia) (Hth80 eq_refl)
                  ltac:(intros M' O'; destruct (HCG eq_refl M' O') as (Q1 & Q2 & Q3 & _); exact (conj Q1 (conj Q2 Q3)))
                  regs H10 H4 H2 H1) as (r' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OJ & GJ).
      exists r', (core5_mem Mj s fs h j pos ff). split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|].
      apply (core5_desc mem0 Mj 1 (s - 208) s s fs h j pos ff col); [|split; assumption | exact Happm | exact Hposb | exact Hff_def].
      apply (gc_post_ext 1 mem0 Mj (s - 208) s fs (fun _ _ => False) col); [intros c i _; split; [intros X; exact (NC c i X) | intros []]|].
      apply (gc_post_nogc_5 1 mem0 Mj (s - 208) s fs GJ OJ); [lia | lia | lia | exact Hng'].
    - (* [comment removed for export] *)
      assert (EC : forall c i, gc_valid c i -> (col c i <-> gc_col s botth flag rs c i)) by (intros c i _; unfold fsm5_colg; split; [intros (_ & _ & X); exact X | intros X; split; [exact EG | split; [exact SCAN | exact X]]]).
      destruct (Htop eq_refl) as (Tp1 & Tp2 & Tp3 & Tp4).
      destruct (fsm5_gcc_run mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd
                  Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng' Hssl Hhint HF0
                  ltac:(intros i Hi; destruct (Hprobe i Hi) as [A B]; split; [exact A | intros X; apply B; apply (fun V => proj2 (EC _ _ V)); [|exact X]; split; [lia | pw (2 ^ (14 - CLS))%Z; apply Z.mod_pos_bound; lia]])
                  ltac:(destruct Hflag as [A|B]; [left; exact A | right; apply (proj1 (EC CLS pos Vpos)); exact B])
                  Hwfs HG Hshadow_ok ltac:(lia) (Hth80 eq_refl) (HCG eq_refl) (HRS eq_refl)
                  ltac:(intros c i Vc Cc; apply (Hcol6 c i Vc); apply (proj2 (EC c i Vc)); exact Cc)
                  ltac:(intros c i Vc Cc; apply (Hshok c i Vc); apply (proj2 (EC c i Vc)); exact Cc)
                  regs H10 H4 H2 H1) as (r' & Mg & RUN & Q10 & Q2 & Q1 & KCS & GP).
      exists r', (core5_mem Mg s fs h j pos ff). split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|].
      apply (core5_desc mem0 Mg 0 (s - 208) s s fs h j pos ff col); [|split; assumption | exact Happm | exact Hposb | exact Hff_def].
      apply (gc_post_ext 0 mem0 Mg (s - 208) s fs (gc_col s botth flag rs) col EC GP).
    - (* [comment removed for export] *)
      assert (NC : forall c i, ~ col c i) by (intros c i [X _]; rewrite EG in X; discriminate X).
      destruct (NOSCAN NC) as [CP C4].
      destruct (fsm5_gen_run mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd
                  Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff Hfs Hh Hj Hpos_def Hff_def Hng' Hssl Hhint CP C4 Hwfs HG INAPP Hshadow_ok
                  ltac:(lia) regs H10 H4 H2 H1) as (r' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OJ & GJ).
      exists r', (core5_mem Mj s fs h j pos ff). split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|].
      apply (core5_desc mem0 Mj 0 (s - 208) s s fs h j pos ff col); [|split; assumption | exact Happm | exact Hposb | exact Hff_def].
      apply (gc_post_ext 0 mem0 Mj (s - 208) s fs (fun _ _ => False) col); [intros c i _; split; [intros X; exact (NC c i X) | intros []]|].
      apply (gc_post_nogc_5 0 mem0 Mj (s - 208) s fs GJ OJ); [lia | lia | lia | exact Hng'].
  Qed.
End RUN5.
End FPX_1.
