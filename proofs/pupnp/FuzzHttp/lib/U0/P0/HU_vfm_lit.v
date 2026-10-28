From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype H_scanner_get_token H_vfmatch_A HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Ltac vfl_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 0 0) with 0.

Section VFL.
Context {HCEIL : HasCeiling}.

  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis VOK : vf_ok q lo S MB A len cap cur0 bs.

  Notation qq := (q + -208)%Z.
  Notation W0 := [(q - 304, q - 104); (S + 8, S + 16)]%Z.
  Notation dpost := (dpost q lo S MB A len cap cur0 bs).
  Notation linv := (linv q lo S MB A len cap bs).
  Notation headst := (headst q S cur0). Notation contst := (contst q S cur0). Notation exitst := (exitst q S cur0).
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs). Notation FX := (FX q).
  Notation F0 := (F0 q). Notation F36 := (F36 q). Notation F40 := (F40 q). Notation F56 := (F56 q).
  Notation F72 := (F72 q). Notation F76 := (F76 q). Notation F84 := (F84 q). Notation F88 := (F88 q).

  #[using="VOK"] Lemma dir_lit : forall (fp c G cs cur : Z) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 cs -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    (0 < c < 256)%Z -> c <> 9 -> c <> 32 -> c <> 37 ->
    evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => (r = 1 /\ cur' = cur) \/ ((r = 4 \/ r = 5) /\ cur' = cur + 1))%Z (fun _ => False) m)
        (headst gp tp F fc fp c G x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS CR N9 N32 N37. unf.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    zstep. if_cases K; zify_cond K. { exfalso; lia. }
    zstep. if_cases K'; zify_cond K'. { exfalso; lia. }
    zstep. if_cases K''; zify_cond K''. 2:{ exfalso; lia. }
    zstep. ub_null. ub_align.
    zstep. zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
    { dfinish 1 cur. }
    destruct (nth_bs q lo S MB A len cap cur0 bs VOK cur ltac:(lia)) as [b0 Hb0]. pose proof (byte_range b0) as BR0.
    zstep. zstep. zstep. sstep.
    step. ubr.
    zstep. zstep. zstep. vfl_b2z. step. lit_branch.
    step. ubr.
    pose proof (u8ro_read rsegs _ A bs cur b0 (Z_to_bv 64 (A + cur)) BUF Hb0 ltac:(lia) eq_refl) as RD0.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    - assert (CS0 : cs = 0) by lia. subst cs.
      zstep. zstep. call tolower_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
      zstep. zstep. zstep. call tolower_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
      sstep. zstep. zstep. zstep. zstep. zstep.
      match goal with |- context [Z_to_bv 64 (Z.lxor (Z.b2z ?bb) 5)] => rewrite (lxor_b2z_5 bb); destruct bb end.
      * dfinish 4 (cur + 1)%Z. * dfinish 5 (cur + 1)%Z.
    - zstep. zstep. zstep. zstep. zstep. zstep.
      match goal with |- context [Z_to_bv 64 (Z.lxor (Z.b2z ?bb) 5)] => rewrite (lxor_b2z_5 bb); destruct bb end.
      * dfinish 4 (cur + 1)%Z. * dfinish 5 (cur + 1)%Z.
  Qed.
End VFL.
