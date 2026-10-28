(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma forgets_length : forall sl sl', forgets sl sl' -> length sl' = length sl.
Proof. intros sl sl' H. induction H; cbn [length]; congruence. Qed.
Lemma MEMI_forgets : forall E nxt sl sl' sc fc m1, MEMI E nxt sl sc fc m1 -> cells_size (fr_cells E sl) = 312%nat -> forgets (fr_cells E sl) (fr_cells E sl') ->
  MEMI E nxt sl' sc fc m1.
Proof.
  intros E nxt sl sl' sc fc m1 (FRM & FR & REST) _ H. split; [exact FRM|]. split; [|exact REST].
  eapply rw_cells_forgets; [exact H| exact FR].
Qed.

Section Write.
  Variable E : s2env.
  Hypothesis OK : env_ok E.

  Ltac wk_env :=
    pose proof (ok_spa _ OK) as Espa; pose proof (ok_sptop _ OK) as Etop; pose proof (ok_ff _ OK) as Eff;
    pose proof (ok_this _ OK) as Ethis; pose proof (ok_doc _ OK) as Edoc; pose proof (ok_idx _ OK) as Eidx;
    pose proof (ok_buf _ OK) as Ebuf; pose proof (ok_tape _ OK) as Etape; pose proof (ok_sbuf _ OK) as Esbuf; pose proof (ok_oc _ OK) as Eoc;
    pose proof (ok_ia _ OK) as Eia; pose proof (ok_tcap _ OK) as Etcap; pose proof (ok_scap _ OK) as Escap;
    unfold S2_LEN_MAX in *;
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR.

  Lemma MEMI_sbuf_write : forall nxt sl sc fc (m : mem) (i : Z) (a : word) bs (n : nat),
    cells_size (fr_cells E sl) = 312%nat -> length bs = n -> (0 <= i)%Z -> (i + Z.of_nat n <= e_scap E)%Z -> a = wa (e_SBUF E + i) ->
    (Z.of_nat (length (e_sbs E)) <= i)%Z ->
    MEMI E nxt sl sc fc m -> MEMI E nxt sl sc fc (write_to_mem m a bs).
  Proof using OK.
    intros nxt sl sc fc m i a bs n HSL HN Hi0 Hi1 -> HG (FRM & FR & SAV & GAP & FFW & IMPL & DOCC & IDXA & BUFRO & TAPEW & SBUFW & (ocs & OCA & OCL & OCR) & (ias & IAA & IAL & IAR) & MI & MU & WM & ST & TIMG).
    wk_env. subst n.
    assert (A0 : (0 <= e_SBUF E + i)%Z) by lia.
    assert (A1 : (e_SBUF E + i + Z.of_nat (length bs) <= 2 ^ 64)%Z) by lia.
    split; [exact FRM|].
    split. { apply rw_cells_frame; [exact FR| exact A0| exact A1|]. rewrite HSL. lia. }
    split. { apply rw_cells_frame; [exact SAV| exact A0| exact A1|]. cbn [saved_cells cells_size csize Nat.add]. lia. }
    split. { apply stk_write; [exact GAP| exact A0| exact A1]. }
    split. { apply wr_at_write. exact FFW. }
    split. { apply rw_cells_frame; [exact IMPL| exact A0| exact A1|]. cbn [impl_cells cells_size csize Nat.add]. pose proof (ok_d_this_sbuf _ OK). lia. }
    split. { apply rw_cells_frame; [exact DOCC| exact A0| exact A1|]. cbn [doc_cells cells_size csize Nat.add]. pose proof (ok_d_doc_sbuf _ OK). lia. }
    split. { apply u32arr_frame; [exact IDXA| exact A0| exact A1|]. pose proof (ok_d_sbuf_idx _ OK). lia. }
    split. { apply bytes_at_write_other; [exact BUFRO| exact A0| exact A1|]. rewrite padded_bytes_blen. pose proof (ok_d_sbuf_buf _ OK). lia. }
    split. { apply wr_at_write. exact TAPEW. }
    split. { apply wr_at_write. exact SBUFW. }
    split. { exists ocs. split; [|split; [exact OCL| exact OCR]]. apply u32arr_frame; [exact OCA| exact A0| exact A1|]. rewrite OCL. pose proof (ok_d_sbuf_oc _ OK). lia. }
    split. { exists ias. split; [|split; [exact IAL| exact IAR]]. apply u8arr_frame; [exact IAA| exact A0| exact A1|]. rewrite IAL. pose proof (ok_d_sbuf_ia _ OK). lia. }
    split. { apply mem_inv_store; [exact MI|]. apply (wr_at_store_ok bsegs m (e_SBUF E) (e_scap E) i (length bs) SBUFW); lia. }
    split. { apply munch_write; [exact MU| exact A0| exact A1|]. unfold s2_W. cbn [inside]. right. right. right. left. lia. }
    split. { apply wmono_write. exact WM. }
    split. { apply stk_write; [exact ST| exact A0| exact A1]. }
    apply (tape_img_write_sbuf E OK _ _ m _ bs (Z.of_nat (length bs)) eq_refl A0 A1 TIMG). lia.
  Qed.

  Lemma MEMI_tape_write : forall nxt sl sc fc (m : mem) (i : Z) (a : word) bs (n : nat),
    cells_size (fr_cells E sl) = 312%nat -> length bs = n -> (0 <= i)%Z -> (i + Z.of_nat n <= 8 * e_tcap E)%Z -> a = wa (e_TAPE E + i) ->
    (8 * Z.of_nat (length (e_tws E)) <= i)%Z ->
    MEMI E nxt sl sc fc m -> MEMI E nxt sl sc fc (write_to_mem m a bs).
  Proof using OK.
    intros nxt sl sc fc m i a bs n HSL HN Hi0 Hi1 -> HG (FRM & FR & SAV & GAP & FFW & IMPL & DOCC & IDXA & BUFRO & TAPEW & SBUFW & (ocs & OCA & OCL & OCR) & (ias & IAA & IAL & IAR) & MI & MU & WM & ST & TIMG).
    wk_env. subst n.
    assert (A0 : (0 <= e_TAPE E + i)%Z) by lia.
    assert (A1 : (e_TAPE E + i + Z.of_nat (length bs) <= 2 ^ 64)%Z) by lia.
    split; [exact FRM|].
    split. { apply rw_cells_frame; [exact FR| exact A0| exact A1|]. rewrite HSL. lia. }
    split. { apply rw_cells_frame; [exact SAV| exact A0| exact A1|]. cbn [saved_cells cells_size csize Nat.add]. lia. }
    split. { apply stk_write; [exact GAP| exact A0| exact A1]. }
    split. { apply wr_at_write. exact FFW. }
    split. { apply rw_cells_frame; [exact IMPL| exact A0| exact A1|]. cbn [impl_cells cells_size csize Nat.add]. pose proof (ok_d_this_tape _ OK). lia. }
    split. { apply rw_cells_frame; [exact DOCC| exact A0| exact A1|]. cbn [doc_cells cells_size csize Nat.add]. pose proof (ok_d_doc_tape _ OK). lia. }
    split. { apply u32arr_frame; [exact IDXA| exact A0| exact A1|]. pose proof (ok_d_tape_idx _ OK). lia. }
    split. { apply bytes_at_write_other; [exact BUFRO| exact A0| exact A1|]. rewrite padded_bytes_blen. pose proof (ok_d_tape_buf _ OK). lia. }
    split. { apply wr_at_write. exact TAPEW. }
    split. { apply wr_at_write. exact SBUFW. }
    split. { exists ocs. split; [|split; [exact OCL| exact OCR]]. apply u32arr_frame; [exact OCA| exact A0| exact A1|]. rewrite OCL. pose proof (ok_d_tape_oc _ OK). lia. }
    split. { exists ias. split; [|split; [exact IAL| exact IAR]]. apply u8arr_frame; [exact IAA| exact A0| exact A1|]. rewrite IAL. pose proof (ok_d_tape_ia _ OK). lia. }
    split. { apply mem_inv_store; [exact MI|]. apply (wr_at_store_ok bsegs m (e_TAPE E) (8 * e_tcap E) i (length bs) TAPEW); lia. }
    split. { apply munch_write; [exact MU| exact A0| exact A1|]. unfold s2_W. cbn [inside]. right. right. left. lia. }
    split. { apply wmono_write. exact WM. }
    split. { apply stk_write; [exact ST| exact A0| exact A1]. }
    apply (tape_img_write_tape E OK _ _ m _ bs (Z.of_nat (length bs)) eq_refl A0 A1 TIMG). lia.
  Qed.

End Write.

Ltac wk_len bs :=
  lazymatch bs with
  | le8 _ => constr:(8%nat) | le4 _ => constr:(4%nat) | le2 _ => constr:(2%nat) | le1 _ => constr:(1%nat)
  | [_] => constr:(1%nat) | Z_to_le_bytes ?k _ => constr:(k) end.
Ltac wk_clear m :=
  repeat match goal with
  | H : context [m] |- _ => clear H
  end;
  repeat match goal with
  | H : frm0 _ |- _ => clear H
  | H : length _ = 2048%nat |- _ => clear H
  | H : length _ = 1024%nat |- _ => clear H
  | H : oc_rel _ _ |- _ => clear H
  | H : ia_rel _ _ |- _ => clear H
  | H : Z.of_nat (length (padded_bytes _)) = _ |- _ => clear H
  end.
Ltac wk_store_done :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      lazymatch goal with
      | HMh : MEMI ?E ?nxt ?sl ?sc ?fc m, OKh : env_ok ?E |- _ =>
          let Ea := addr_expr a in
          let n := wk_len bs in
          let HM' := fresh "HMW" in
          first
          [ (let idx := strip_base Ea (e_SBUF E) in
             assert (HM' : MEMI E nxt sl sc fc (write_to_mem m a bs))
               by (apply (MEMI_sbuf_write E OKh nxt sl sc fc m idx a bs n eq_refl eq_refl);
                   [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold wa; f_equal; lia | lia | exact HMh]))
          | (let idx := strip_base Ea (e_TAPE E) in
             assert (HM' : MEMI E nxt sl sc fc (write_to_mem m a bs))
               by (apply (MEMI_tape_write E OKh nxt sl sc fc m idx a bs n eq_refl eq_refl);
                   [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold wa; f_equal; lia | lia | exact HMh])) ];
          let m' := fresh "m" in
          set (m' := write_to_mem m a bs) in *; clearbody m';
          wk_clear m;
          let HMo := fresh "HMo" in pose proof HM' as HMo; s2_open_mem HMo
      end
  end.

Ltac wk_note_transport m a Ea bs n :=
  repeat match goal with
  | H : bytes_at ?segs m ?A2 ?bs2 |- _ =>
      lazymatch A2 with
      | context [e_TAPE _] => idtac | context [e_SBUF _] => idtac
      end;
      first [ apply (bytes_at_write_other_n segs m Ea bs A2 bs2 n) in H;
              [ replace (write_to_mem m (wa Ea) bs) with (write_to_mem m a bs) in H by (f_equal; unfold wa; f_equal; lia)
              | reflexivity | tlia | tlia | simpl_sizes; rewrite ?length_le8, ?length_le4, ?length_le1; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; tlia ]
            | fail 100 "wk_note_transport: cannot move the noted chunk" H "across the store at" Ea ]
  end.
Ltac wk_store_done_note :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let n := wk_len bs in
      let bs' := lazymatch bs with
                 | Z_to_le_bytes 8 ?lit => constr:(le8 (Z_to_bv 64 lit))
                 | Z_to_le_bytes 4 ?lit => constr:(le4 (Z_to_bv 64 lit))
                 | Z_to_le_bytes 1 ?lit => constr:(le1 (Z_to_bv 64 lit))
                 | _ => bs end in
      let Ea := addr_expr a in
      wk_note_transport m a Ea bs (Z.of_nat n);
      let NW := fresh "WCH" in
      assert (NW : bytes_at segs (write_to_mem m (wa Ea) bs) Ea bs')
        by (change bs' with bs; apply bytes_at_write_same; [tlia | simpl_sizes; rewrite ?length_Z_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; tlia]);
      replace (write_to_mem m (wa Ea) bs) with (write_to_mem m a bs) in NW by (f_equal; unfold wa; f_equal; lia);
      wk_store_done
  end.

Ltac wk_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store_fast
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store_fast
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store_fast
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store_fast
  end.
Ltac wk_maybe_store_done :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => first [ wk_store_done | wk_lit_store ]
  | _ => idtac
  end.

Ltac wk_refold :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      tryif is_var m then
        lazymatch goal with
        | HMh : MEMI _ _ _ _ _ m |- _ => idtac
        | HMs : MEMI ?E ?nxt _ ?sc ?fc _ |- _ =>
            lazymatch goal with
            | FRh : rw_cells _ m (e_SP E) (?c0 :: ?c8 :: ?c16 :: ?c24 :: ?c32 :: ?c40 :: ?c48 :: ?c56 :: ?c64 :: ?c72 :: ?c80 :: ?c88 :: ?c96 :: ?c104 :: ?c112 :: ?c120 :: ?c128 :: ?c136 :: ?c144 :: ?c152 :: ?c160 :: ?c168 :: ?c176 :: ?c184 :: ?c192 :: ?c200 :: ?k208 :: ?k216 :: ?k224 :: ?k232 :: ?k240 :: ?k248 :: ?k256 :: ?k264 :: ?c272 :: ?k280 :: ?c288 :: ?k296 :: ?c304 :: _) |- _ =>
                let HM' := fresh "HMW" in
                assert (HM' : MEMI E nxt [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288; c304] sc fc m) by (s2_close_mem; eassumption);
                repeat match goal with HMo : MEMI _ _ _ _ _ ?mo |- _ => lazymatch mo with m => fail | _ => clear HMo end end
            end
        | _ => idtac
        end
      else idtac
  end.
Ltac wstep := zstep; gnorm; wk_maybe_store_done; wk_refold.

Ltac wk_maybe_store_done_note :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a _) _) =>
      let Ea := addr_expr a in let b := addr_leaf Ea in
      lazymatch b with
      | e_TAPE _ => wk_store_done_note
      | e_SBUF _ => wk_store_done_note
      | _ => first [ wk_store_done | wk_lit_store ]
      end
  | _ => idtac
  end.
Ltac wstep_note := zstep; gnorm; wk_maybe_store_done_note; wk_refold.
Ltac wrun := repeat first [ gguard | wstep ].
Ltac wrun_to A :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          first [ gguard | wstep ]).

Ltac wrun_note_to A :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          first [ gguard | wstep_note ]).

Ltac wk_close := eapply MEMI_forgets; [ eassumption | reflexivity | unfold fr_cells; forgets_tac ].

Ltac gproj :=
  cbn [e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA
       e_bs e_idxs e_iws e_tcap e_scap e_vptr e_p12 e_nxt0 e_p28 e_capv e_p50 e_dcap e_j0 e_j256 e_m0 e_tws e_sbs s2_ghost gapp gpatch].
Ltac wk_close_ghost :=
  unfold empty_env, endc_env, gapp; eapply MEMI_forgets;
  [ eapply MEMI_ghost; [ gproj; eassumption | gproj; first [ eassumption | rewrite ?app_nil_r in *; eassumption ] ]
  | reflexivity
  | gproj; unfold fr_cells; forgets_tac ].

Lemma str_byte_ku : forall d kk, (0 <= d < 2^31)%Z -> (0 <= kk)%Z ->
  (bv_unsigned (Z_to_bv 64 (Z.shiftr d kk)) mod 256 = (d / 2^kk) mod 256)%Z.
Proof.
  intros d kk Hd Hk. pose proof (str_byte_k d kk Hd Hk) as P. rewrite (Z.mod_small d) in P by lia. exact P.
Qed.

Ltac s2_str_close d :=

  repeat match goal with
  | N : bytes_at _ ?m ?A (le1 (Z_to_bv 64 ?dv)) |- _ =>
      lazymatch dv with
      | d => fail
      | 0%Z => fail
      | Z.shiftr d _ => fail
      | Z.shiftr (d mod 18446744073709551616) ?kk => change (Z.shiftr (d mod 18446744073709551616) kk) with (Z.shiftr d kk) in N
      | Z.shiftr (?dv2 mod 18446744073709551616) ?kk => replace (Z.shiftr (dv2 mod 18446744073709551616) kk) with (Z.shiftr d kk) in N by (rewrite (Z.mod_small dv2) by lia; f_equal; lia)
      | Z.shiftr ?dv2 ?kk => replace dv2 with d in N by lia
      | _ => replace dv with d in N by lia
      end
  end;
  match goal with
  | OKh : env_ok ?E, TI : tape_img ?E ?tws ?sbs ?m,
    N0 : bytes_at _ ?m ?A (le1 (Z_to_bv 64 d)),
    N1 : bytes_at _ ?m ?A1 (le1 (Z_to_bv 64 (Z.shiftr d 8))),
    N2 : bytes_at _ ?m ?A2 (le1 (Z_to_bv 64 (Z.shiftr d 16))),
    N3 : bytes_at _ ?m ?A3 (le1 (Z_to_bv 64 (Z.shiftr d 24))),
    NN : bytes_at _ ?m ?AN (le1 (Z_to_bv 64 0)) |- _ =>
      let cb := fresh "cb" in let HCL := fresh "HCL" in let HCB := fresh "HCB" in let SRL := fresh "SRL" in let TI2 := fresh "TIMG" in
      destruct (timg_sbytes E tws sbs m (Z.of_nat (length sbs) + 4) d TI ltac:(lia) ltac:(lia) ltac:(lia)) as (cb & HCL & HCB);
      replace A1 with (A + 1)%Z in N1 by lia; replace A2 with (A + 2)%Z in N2 by lia; replace A3 with (A + 3)%Z in N3 by lia;
      replace AN with (A + 4 + d)%Z in NN by lia;
      replace (e_SBUF E + (Z.of_nat (length sbs) + 4))%Z with (A + 4)%Z in HCB by lia;
      pose proof (tape_img_app_str E tws sbs m d cb _ _ _ _ A TI ltac:(lia) N0 N1 N2 N3 HCB HCL NN
                    ltac:(rewrite u64_small by lia; reflexivity)
                    ltac:(apply (str_byte_ku d 8); lia) ltac:(apply (str_byte_ku d 16); lia) ltac:(apply (str_byte_ku d 24); lia)
                    ltac:(lia) ltac:(lia) ltac:(lia)) as TI2;
      clear TI N0 N1 N2 N3 NN HCB;
      assert (SRL : Z.of_nat (length (map bv_unsigned cb)) = d) by (rewrite length_map; exact HCL)
  | |- _ => fail 100 "s2_str_close: the noted length bytes / NUL / tape image are not in the context"
  end.

Ltac s2_str_word sbv :=
  match goal with
  | N : bytes_at _ ?m ?A (le8 (Z_to_bv 64 (Z.lor ?x 2449958197289549824%Z))) |- _ =>
      replace (Z.lor x 2449958197289549824%Z) with (tword t_str sbv) in N by (rewrite <- (str_word_machine 0%Z sbv) by lia; f_equal; lia)
  | N : bytes_at _ ?m ?A (le8 (Z_to_bv 64 2449958197289549824%Z)) |- _ =>
      change 2449958197289549824%Z with (tword t_str 0) in N
  | |- _ => fail 100 "s2_str_word: no noted string tape word"
  end.

Ltac s2_tape1 w :=
  match goal with
  | OKh : env_ok ?E0, TI : tape_img ?E0 ?tws ?sbs ?m, N1 : bytes_at _ ?m ?A1 (le8 (Z_to_bv 64 w)) |- _ =>
      apply (tape_img_app1 E0 tws sbs m w A1 OKh TI) in N1; [ clear TI; rename N1 into TI | tlia | tlia | first [apply tword_range; unfold t_str; tlia | tlia] ]
  | _ => fail 100 "s2_tape1: no noted tape chunk with that word right after the written prefix"
  end.

Ltac s2_tape_hole1 w :=
  match goal with
  | OKh : env_ok ?E0, TI : tape_img ?E0 ?tws ?sbs ?m, N1 : bytes_at _ ?m ?A1 (le8 (Z_to_bv 64 w)) |- _ =>
      let hv := fresh "hv" in let HH := fresh "HH" in let HVR := fresh "HVR" in
      destruct (timg_hole8 E0 tws sbs m (Z.of_nat (length tws)) TI ltac:(tlia)) as (hv & HH);
      pose proof (bv_unsigned_in_range 64 hv) as HVR; unfold bv_modulus in HVR; cbn in HVR;
      rewrite <- (Z_to_bv_bv_unsigned hv) in HH;
      apply (tape_img_app2 E0 tws sbs m (bv_unsigned hv) w _ A1 OKh TI HH) in N1;
      [ clear TI HH; rename N1 into TI | tlia | tlia | tlia | tlia | first [apply tword_range; unfold t_str; tlia | tlia] ]
  | _ => fail 100 "s2_tape_hole1: no noted tape chunk with that word one word after the written prefix"
  end.

Ltac s2_ghost_bundle :=
  match goal with
  | HMh : MEMI ?E ?nxt ?sl ?sc ?fc ?m, TI : tape_img ?E ?tws ?sbs ?m |- _ =>
      let HME := fresh "HME" in pose proof (MEMI_ghost E tws sbs nxt sl sc fc m HMh TI) as HME
  | _ => fail 100 "s2_ghost_bundle: no folded bundle / image for the current memory"
  end.

Ltac if_cases_eq K :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if negb ?c then _ else _) _ _ _ _) =>
      destruct c eqn:K;
      lazymatch goal with
      | |- evt ?s ?Q (MS ?R ?F (if negb true then ?a else ?b) ?fc ?rv ?m ?ro) => change (evt s Q (MS R F b fc rv m ro))
      | |- evt ?s ?Q (MS ?R ?F (if negb false then ?a else ?b) ?fc ?rv ?m ?ro) => change (evt s Q (MS R F a fc rv m ro))
      end
  | _ => if_cases K
  end;
  zify_cond K.

Ltac wrun_to2 A B :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | B => fail | _ => idtac end
          | _ => idtac end;
          first [ gguard | wstep ]).
