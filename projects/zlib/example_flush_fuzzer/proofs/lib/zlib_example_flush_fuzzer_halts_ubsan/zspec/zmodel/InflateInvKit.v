(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Lemma ck_adl_init : ck_adl iadler32_init. Proof. right; left; reflexivity. Qed.
Lemma ck_adl_crc0 : ck_adl icrc32_init. Proof. left; reflexivity. Qed.
Lemma ck_adl_upd : forall a bs, ck_adl (iadler32_upd a bs). Proof. intros a bs. right; right. exists a, bs. reflexivity. Qed.
Lemma ck_adl_UPD : forall s ck bs, is_flags s = 0 -> ck_adl (UPDATE_CHECK_bytes s ck bs).
Proof. intros s ck bs H. unfold UPDATE_CHECK_bytes. rewrite H. cbn. apply ck_adl_upd. Qed.

Global Opaque bkv sbv tab_ok tables_okf ctab_okf cat icrc32_upd iadler32_upd UPDATE_CHECK_bytes ZSWAP32 crc32_model adler32_model.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition apost (NI NO WN TOT0 : Z) (w : iw) (a : ares unit) : Prop :=
  match a with
  | ARun _ w' => pinv NI NO WN TOT0 w' /\ PHI w' < PHI w
  | ALeave w' => LRNGq NI NO WN TOT0 w' /\ sinv (w_s w') /\ binv w' /\ cks (w_s w')
  | ARet _ w' => LRNGq NI NO WN TOT0 w' /\ sinv (w_s w') /\ binv w'
                 /\ (is_hold (w_s w') = ir_hold (w_r w') /\ is_bits (w_s w') = ir_bits (w_r w')) /\ cks (w_s w')
  end.

Definition wle (w w' : iw) : Prop :=
  ir_left (w_r w') <= ir_left (w_r w) /\ ir_bits (w_r w') + 8 * ir_have (w_r w') <= ir_bits (w_r w) + 8 * ir_have (w_r w).
Lemma wle_refl : forall w, wle w w.
Proof. intros w. unfold wle. lia. Qed.
Lemma wle_trans : forall w1 w2 w3, wle w1 w2 -> wle w2 w3 -> wle w1 w3.
Proof. intros w1 w2 w3 [A B] [C D]. unfold wle. lia. Qed.
Lemma PHI_wle : forall w w', wle w w' -> PHI w' - mrank (is_mode (w_s w')) <= PHI w - mrank (is_mode (w_s w)).
Proof. intros w w' [A B]. unfold PHI. lia. Qed.

Lemma apost_mono : forall NI NO WN TOT0 wm w a,
  PHI wm <= PHI w -> apost NI NO WN TOT0 wm a -> apost NI NO WN TOT0 w a.
Proof. intros NI NO WN TOT0 wm w [u w'|w'|rc w'] H A; cbn [apost] in *; [| exact A | exact A]. destruct A as [P M]. split; [exact P | lia]. Qed.


Ltac wred0 :=
  cbv beta iota zeta delta [abind aret gs gc gr us ur uc aleave areturn amodify agets aget aput
       set_mode set_msg go_bad set_adler_check BITS HOLD DROPBITS INITBITS BYTEBITS aux fixedtables hcrc_on
       crc_input CRC2 CRC4 DECODE1 DECODE2 set_lens
       w_s w_c w_r wset_s wset_r wset_c
       is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk
       iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits iset_wsize
       iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode
       iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work
       iset_codes iset_sane iset_back iset_was iset_self_blk
       ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg
       icset_input icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out icset_adler
       icset_data_type icset_msg
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret
       irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret].
Ltac bsimp := cbn [andb orb negb xorb Z.eqb Z.ltb Z.leb Z.compare Pos.compare Pos.compare_cont Pos.eqb].
Ltac wred := wred0; bsimp.
Tactic Notation "wred" "in" hyp(H) :=
  cbv beta iota zeta delta [abind aret gs gc gr us ur uc aleave areturn amodify agets aget aput
       set_mode set_msg go_bad set_adler_check BITS HOLD DROPBITS INITBITS BYTEBITS aux fixedtables hcrc_on
       crc_input CRC2 CRC4 DECODE1 DECODE2 set_lens
       w_s w_c w_r wset_s wset_r wset_c
       is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk
       iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits iset_wsize
       iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode
       iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work
       iset_codes iset_sane iset_back iset_was iset_self_blk
       ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg
       icset_input icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out icset_adler
       icset_data_type icset_msg
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret
       irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret] in H.

Lemma mode_consts : HEAD = 16180 /\ FLAGS = 16181 /\ TIME = 16182 /\ OS = 16183 /\ EXLEN = 16184 /\ EXTRA = 16185
  /\ NAME = 16186 /\ COMMENT = 16187 /\ HCRC = 16188 /\ DICTID = 16189 /\ DICT = 16190 /\ TYPE = 16191 /\ TYPEDO = 16192
  /\ STORED = 16193 /\ COPY_ = 16194 /\ COPY = 16195 /\ TABLE = 16196 /\ LENLENS = 16197 /\ CODELENS = 16198
  /\ LEN_ = 16199 /\ LEN = 16200 /\ LENEXT = 16201 /\ DIST = 16202 /\ DISTEXT = 16203 /\ MATCH = 16204 /\ LIT = 16205
  /\ CHECK = 16206 /\ LENGTH = 16207 /\ DONE = 16208 /\ BAD = 16209 /\ MEM = 16210 /\ SYNC = 16211.
Proof. repeat split; reflexivity. Qed.
Ltac mlia := cbv delta [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE
                        LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC
                        Z_OK Z_STREAM_END Z_NEED_DICT Z_ERRNO Z_STREAM_ERROR Z_DATA_ERROR Z_MEM_ERROR Z_BUF_ERROR] in *; lia.

Ltac dworld w :=
  let s := fresh "s" in let c := fresh "c" in let r := fresh "r" in
  destruct w as [s c r];
  destruct s as [f_mode f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                 f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                 f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk];
  destruct c as [c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg];
  destruct r as [r_next r_have r_put r_left r_hold r_bits r_in r_out r_ret].

Ltac sinv_open SI :=
  unfold sinv in SI;
  cbn [is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk] in SI;
  destruct SI as (?Wh & ?Wn & (?Alens & ?Awork & ?Acodes) & ?Qtab & ?Qlenlens & ?Qcodelens & ?Qlenext & ?Qdist & ?Qdistext & ?Qmatch & ?Qcopy & ?Qrep & ?Qcrep).
Ltac konly0 := repeat match goal with H : _ |- _ => clear H end.
Ltac triage_dec Q :=
  lazymatch type of Q with ?P -> _ =>
    first [ specialize (Q ltac:(konly0; mlia)) | (assert_succeeds (assert (~ P) by (konly0; mlia)); clear Q) | idtac ] end.
Ltac triage1 Q :=
  first [ specialize (Q eq_refl)
        | specialize (Q (or_introl eq_refl))
        | specialize (Q (or_intror eq_refl))
        | clear Q ].
Ltac pend_red_in H :=
  cbn [PEND Z.eqb Pos.eqb orb w_s w_r ir_bits ir_hold is_mode is_wrap is_flags is_extra is_have is_nlen is_ndist is_hold is_bits
       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS
       LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in H.
Ltac pend_red :=
  cbn [PEND Z.eqb Pos.eqb orb w_s w_r ir_bits ir_hold is_mode is_wrap is_flags is_extra is_have is_nlen is_ndist is_hold is_bits
       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS
       LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC].
Ltac sinv_triage :=
  match goal with Qtab : codes_live _ = true -> tables_ok _ = true |- _ => triage1 Qtab | _ => idtac end;
  match goal with Q : codes_live _ = true -> tables_rep _ |- _ => triage1 Q | _ => idtac end;
  match goal with Q : _ = CODELENS -> ctab_rep _ |- _ => triage1 Q | _ => idtac end;
  match goal with Q : _ \/ PEND _ _ _ _ |- _ => pend_red_in Q | _ => idtac end;
  match goal with Q : _ = LENLENS -> _ |- _ => triage1 Q | _ => idtac end;
  match goal with Q : _ = CODELENS -> _ /\ _ |- _ => triage1 Q | _ => idtac end;
  match goal with Q : _ = LENEXT -> _ |- _ => triage1 Q | _ => idtac end;
  match goal with Q : _ = DIST -> _ |- _ => triage1 Q | _ => idtac end;
  match goal with Q : _ = DISTEXT -> _ |- _ => triage1 Q | _ => idtac end;
  match goal with Q : _ = MATCH -> _ |- _ => triage1 Q | _ => idtac end;
  match goal with Q : _ = COPY_ \/ _ = COPY -> _ |- _ => triage1 Q | _ => idtac end;
  match goal with Q : _ <= DICT -> _ = _ |- _ => triage_dec Q | _ => idtac end;
  match goal with Q : MEM <= _ -> _ /\ _ |- _ => triage_dec Q | _ => idtac end.

Ltac pinv_open_rest B LR SI XI KI :=
  apply LRNGq_iff in LR; destruct LR as (SR & CI & RI & WI & CR);
  pose proof RI as RIr; pose proof CI as CIr;
  cbn [w_s w_c w_r] in SI, XI; pose proof SI as SIr; sinv_open SI;
  unfold SRNGq in SR;
  cbn [is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk] in SR;
  destruct SR as (Smode & Slast & Swrap & Shd & Sflags & Sdmax & Scheck & Stotal & Swbits & Swsize & Swhave & Swnext & Shold & Sbits
                  & Slength & Soffset & Sextra & Slenc & Sdistc & Slenbits & Sdistbits & Sncode & Snlen & Sndist & Shave & Snext
                  & Sarrb & Ssane & Sback & Swas & Shead & Swinb & Swhn & Swnh);
  unfold CINV in CI;
  cbn [ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg] in CI;
  destruct CI as (ClNI & ClNO & Cni & Cai & Cnai & Cno & Cao & Cnao & Cinb & Coutb & Cti & Cto & Cad & Cdt);
  unfold RINV in RI; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in RI;
  destruct RI as (Rnx & Rhv & Rnh & Rpt & Rlf & Rpl & Rin & Rout & Rol & Rbits & Rhold);
  unfold WINV in WI; cbn [is_window is_wbits is_window_blk is_wsize] in WI;
  unfold CROSS in CR; cbn [ic_total_out ir_out ir_left ir_put] in CR;
  unfold xinv in XI; cbn [w_s w_c w_r ir_ret is_mode ic_next_out ir_put ir_out ir_left] in XI;
  destruct XI as (Xret & Xno & Xol);
  unfold cinv, cks in KI; cbn [w_s w_c w_r is_mode is_wrap is_flags is_check is_hold is_bits ic_next_out ic_avail_in ic_avail_out
                                ir_put ir_out ir_left ir_have ir_hold ir_bits] in KI;
  destruct KI as (Yck & Yhdr & Yms & Yxck & Yhv & Ylf);
  pose proof mode_consts as (Khead & Kflags & Ktime & Kos & Kexlen & Kextra & Kname & Kcomment & Khcrc & Kdictid & Kdict & Ktype & Ktypedo & Kstored & Kcopy_ & Kcopy & Ktable & Klenlens & Kcodelens & Klen_ & Klen & Klenext & Kdist & Kdistext & Kmatch & Klit & Kcheck & Klength & Kdone & Kbad & Kmem & Ksync).
Ltac pinv_open PI :=
  let B := fresh "B" in let LR := fresh "LR" in let SI := fresh "SI" in let XI := fresh "XI" in let BI := fresh "BI" in
  let KI := fresh "KI" in
  destruct PI as (B & LR & SI & XI & BI & KI);
  pinv_open_rest B LR SI XI KI.
Ltac pinv0_open PI :=
  let B := fresh "B" in let LR := fresh "LR" in let SI := fresh "SI" in let XI := fresh "XI" in
  let KI := fresh "KI" in
  destruct PI as (B & LR & SI & XI & KI);
  pinv_open_rest B LR SI XI KI.

Ltac conj_split :=
  repeat (lazymatch goal with
          | |- _ <= _ < _ => fail | |- _ <= _ <= _ => fail | |- _ < _ <= _ => fail | |- _ < _ < _ => fail
          | |- _ /\ _ => split
          end).
Ltac atrim :=
  repeat match goal with
         | H : ?T |- _ =>
             lazymatch T with
             | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail
             | @eq Z _ _ => fail | (_ <= _ <= _) => fail | (_ <= _ < _) => fail | (_ < _ <= _) => fail | (_ < _ < _) => fail
             | not _ => fail | _ /\ _ => fail | _ \/ _ => fail
             | _ => lazymatch type of T with Prop => clear H end
             end
         end.
Ltac liaq_prune_logic :=
  repeat match goal with
         | H : _ -> _ |- _ => clear H
         | H : _ \/ _ |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         end.
Ltac liaq_nonlit e := lazymatch isZcst e with true => fail | _ => idtac end.
Ltac liaq_prune_nl :=
  repeat match goal with
         | H : context [Z.modulo _ ?e] |- _ => liaq_nonlit e; clear H
         | H : context [Z.div _ ?e] |- _ => liaq_nonlit e; clear H
         | H : context [Z.pow _ ?e] |- _ => liaq_nonlit e; clear H
         | H : context [Z.shiftl _ _] |- _ => clear H
         | H : context [Z.shiftr _ _] |- _ => clear H
         end.
Ltac liaq := first [ solve [liaq_prune_logic; liaq_prune_nl; lia] | solve [liaq_prune_logic; lia] | lia ].
Ltac niaq := first [ solve [liaq_prune_logic; liaq_prune_nl; nia] | solve [liaq_prune_logic; nia] | nia ].
Ltac glia := atrim; first [ solve [liaq_prune_logic; lia] | lia ].
Ltac phi_red :=
  unfold PHI, mrank; wred0;
  cbv beta iota delta [Z.eqb Pos.eqb orb
       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS
       LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC].
Ltac phi_auto := phi_red; glia.
Lemma hold64 : forall h b, 0 <= b < 64 -> 0 <= h < 2 ^ b -> 0 <= h < 2 ^ 64.
Proof. intros h b Hb Hh. pose proof (Z.pow_lt_mono_r 2 b 64 ltac:(lia) ltac:(lia)). lia. Qed.
Ltac range_fact :=
  lazymatch goal with
  | |- 0 <= wrap64 _ < _ => apply wrap64_range
  | |- 0 <= wrap32 _ < _ => apply wrap32_range
  | |- 0 <= wrap16 _ < _ => apply wrap16_range
  | |- - _ <= swrap32 _ < _ => apply swrap32_range
  | |- 0 <= icrc32_upd _ [_; _] < _ => apply CRC2_range
  | |- 0 <= icrc32_upd _ [_; _; _; _] < _ => apply CRC4_range
  | |- 0 <= ZSWAP32 _ < _ => apply ZSWAP32_range
  | |- 0 <= iadler32_upd _ _ < _ => apply iadler32_upd_range
  | |- 0 <= icrc32_init < _ => unfold icrc32_init; lia
  | |- - _ <= bkv _ _ _ < _ => apply bkv_range; first [assumption | liaq | range_fact]
  | |- - _ <= sbv _ _ _ < _ => apply sbv_range; first [assumption | liaq | range_fact]
  | |- 0 <= iadler32_init < _ => unfold iadler32_init; lia
  | |- 0 <= ?h < 2 ^ 64 =>
      first [ assumption
            | match goal with H : 0 <= h < 2 ^ ?b |- _ =>
                match goal with H' : 0 <= b < 64 |- _ => exact (hold64 h b H' H) end end ]
  end.
Ltac arrb_solve := lazymatch goal with |- ARRB _ _ _ => first [ assumption | (apply ARRB_lens_set; [assumption | first [apply wrap16_range | (clear; lia)]]) | idtac ] end.
Ltac conj_solve := conj_split; first [assumption | arrb_solve | glia | range_fact | auto].
Ltac srng_close := unfold SRNGq; cbn [w_s w_c w_r is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk].
Ltac cinv_close := unfold CINV; cbn [w_s w_c w_r ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg].
Ltac rinv_close := unfold RINV; cbn [w_s w_c w_r ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
Ltac winv_close := unfold WINV; cbn [w_s w_c w_r is_window is_wbits is_window_blk is_wsize].
Ltac cross_close := unfold CROSS; cbn [w_s w_c w_r ic_total_out ir_out ir_left ir_put].
Ltac xinv_close := unfold xinv; cbn [w_s w_c w_r ir_ret is_mode ic_next_out ir_put ir_out ir_left].
Ltac binv_close := unfold binv; pend_red.

Ltac rsimp_in H := cbv beta iota delta [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret
                        irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret] in H.
Ltac rinv_open H :=
  let H' := fresh in pose proof H as H';
  unfold RINV in H'; rsimp_in H';
  destruct H' as (?Qnx & ?Qhv & ?Qnh & ?Qpt & ?Qlf & ?Qpl & ?Qin & ?Qout & ?Qol & ?Qbits & ?Qhold).

Ltac needbits_run n RI NI32 NO32 ClNI Cinb :=
  match goal with |- context [NEEDBITS n (mkW ?s ?c ?r)] =>
    let NB := fresh "NB" in
    pose proof (NEEDBITS_run _ _ NI32 NO32 n s c r RI ltac:(liaq) ClNI Cinb) as NB;
    destruct (NEEDBITS n (mkW s c r)) as [? ?w1|?w1|? ?w1]; [ | | destruct NB]
  end.
Ltac dropbits n RI RI' NI32 NO32 :=
  let Hd := fresh "Hd" in let EW := fresh "EW" in
  lazymatch type of RI with RINV _ _ (mkIR _ _ _ _ ?h ?b _ _ _) =>
    assert (Hd : 0 <= n <= b) by glia;
    pose proof (RINV_drop _ _ NI32 NO32 _ n RI Hd) as [EW RI']; rsimp_in EW; rsimp_in RI';
    rewrite ?EW in *; clear Hd
  end.
Ltac decode_run RI HN NI32 NO32 ClNI Cinb :=
  lazymatch type of HN with forall h, _ -> _ <= ?NB =>
  match goal with |- context [DECODE_k ?k ?p ?index ?need (mkW ?s ?c ?r)] =>
    let DC := fresh "DC" in let H1 := fresh in let H2 := fresh in
    assert (H1 : 0 <= NB <= 56) by liaq;
    assert (H2 : NB <= ir_bits r + 8 * Z.of_nat k) by (cbn; glia);
    pose proof (DECODE_k_run _ _ NI32 NO32 k p index need NB s c r RI H1 H2 HN ClNI Cinb) as DC;
    clear H1 H2;
    destruct (DECODE_k k p index need (mkW s c r)) as [?here ?w1|?w1|? ?w1]; [ | | destruct DC]
  end end.
Ltac decode_arun DC r1 RI1 Hhere Hneed :=
  let S5 := fresh "S" in let E := fresh "E" in let Htc := fresh "Htc" in let Hdhv := fresh "Hdhv" in
  let Hdpre := fresh "Hdpre" in let Hdle := fresh "Hdle" in let Hdmin := fresh "Hdmin" in
  destruct DC as (r1 & E & RI1 & S5 & Htc & Hhere & Hneed & Hdhv & Hdpre & Hdle & Hdmin); match type of E with ?x = _ => subst x end;
  destruct r1 as [?n1 ?h1 ?p1 ?l1 ?ho1 ?b1 ?i1 ?o1 ?rt1];
  unfold same5 in S5; unfold tcons in Htc; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in S5, Htc, Hhere, Hneed, Hdhv, Hdpre, Hdle, Hdmin;
  destruct S5 as (-> & -> & -> & -> & ->).
Ltac decode_aleave DC r1 RI1 :=
  let S5 := fresh "S" in let E := fresh "E" in let Htc := fresh "Htc" in let Hz := fresh "Hz" in
  let Hdlt := fresh "Hdlt" in let Hdpre := fresh "Hdpre" in let Hdle := fresh "Hdle" in
  destruct DC as (r1 & E & RI1 & S5 & Htc & Hz & Hdlt & Hdpre & Hdle); match type of E with ?x = _ => subst x end;
  destruct r1 as [?n1 ?h1 ?p1 ?l1 ?ho1 ?b1 ?i1 ?o1 ?rt1];
  unfold same5 in S5; unfold tcons in Htc; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in S5, Htc, Hz, Hdlt, Hdpre, Hdle;
  destruct S5 as (-> & -> & -> & -> & ->).
Ltac auxstep := first [rewrite add_back_eq | rewrite set_back_eq]; wred.
Ltac needbits_arun NB r1 RI1 :=
  let S5 := fresh "S" in let E := fresh "E" in let Htc := fresh "Htc" in
  let Hnb := fresh "Hnb" in let Hnor := fresh "Hnor" in let Hnhv := fresh "Hnhv" in
  let Hnpre := fresh "Hnpre" in let Hnle := fresh "Hnle" in
  destruct NB as (r1 & E & RI1 & S5 & Htc & Hnb & Hnor & Hnhv & Hnpre & Hnle); match type of E with ?x = _ => subst x end;
  destruct r1 as [?n1 ?h1 ?p1 ?l1 ?ho1 ?b1 ?i1 ?o1 ?rt1];
  unfold same5 in S5; unfold tcons in Htc; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in S5, Htc, Hnb, Hnor, Hnhv, Hnpre, Hnle;
  destruct S5 as (-> & -> & -> & -> & ->).
Ltac needbits_aleave NB r1 RI1 :=
  let S5 := fresh "S" in let E := fresh "E" in let Htc := fresh "Htc" in let Hz := fresh "Hz" in
  let Hnlt := fresh "Hnlt" in let Hnpre := fresh "Hnpre" in let Hnle := fresh "Hnle" in
  destruct NB as (r1 & E & RI1 & S5 & Htc & Hz & Hnlt & Hnpre & Hnle); match type of E with ?x = _ => subst x end;
  destruct r1 as [?n1 ?h1 ?p1 ?l1 ?ho1 ?b1 ?i1 ?o1 ?rt1];
  unfold same5 in S5; unfold tcons in Htc; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in S5, Htc, Hz, Hnlt, Hnpre, Hnle;
  destruct S5 as (-> & -> & -> & -> & ->).
Ltac same5_rw H :=
  unfold same5 in H; cbn [ir_put ir_left ir_in ir_out ir_ret] in H;
  destruct H as (?E1 & ?E2 & ?E3 & ?E4 & ?E5); rewrite ?E1, ?E2, ?E3, ?E4, ?E5 in *.
Ltac sinv_goal :=
  unfold sinv;
  cbn [w_s w_c w_r is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk].
Ltac vacuous := let Hx := fresh in intros Hx; exfalso; clear -Hx; cbv -[Z.le Z.lt Z.ge Z.gt Z.add Z.sub Z.mul Z.pow] in Hx;
  first [discriminate Hx | (destruct Hx as [Hx|Hx]; discriminate Hx)].
Ltac arith_goal :=
  lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac | |- @eq Z _ _ => idtac
  | |- (_ <= _ <= _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac
  | |- not _ => idtac | |- _ \/ _ => idtac | |- False => idtac | |- forall _, _ => idtac
  end.
Ltac sinv_easy :=
  sinv_goal; conj_split;
  try first [ assumption
            | (intros; assumption)
            | vacuous
            | arith_goal; glia
            | (intros; conj_split; solve [assumption | arith_goal; glia]) ].
Ltac xinv_auto :=
  let X := fresh "Xa" in let Y := fresh "Ya" in
  xinv_close;
  split; [ first [ assumption | (left; assumption) | (left; reflexivity) | (right; reflexivity)
                 | match goal with Xret : _ = Z_OK \/ _ = BAD |- _ =>
                     destruct Xret as [X|X]; [left; exact X | exfalso; atrim; mlia] end ] |];
  split; [ glia |];
  try match goal with Xol : _ - _ = _ \/ (_ = _ /\ CHECK <= _) |- _ => destruct Xol as [X|[X Y]] end;
  first [ assumption | (left; glia) | (right; split; [glia | mlia]) | (exfalso; mlia) ].

Ltac chain2 P :=
  lazymatch type of P with forall w, ?PINV w -> _ =>
  lazymatch goal with |- _ _ (_ ?w) =>
    let PW := fresh "PW" in
    enough (PW : PINV w); [eapply apost_mono; [| exact (proj2 (P w PW eq_refl))]; try phi_auto | ]
  end end.
Ltac chain1 P :=
  lazymatch type of P with forall w, ?PINV w -> _ =>
  lazymatch goal with |- _ _ (_ ?w) =>
    let PW := fresh "PW" in
    enough (PW : PINV w); [eapply apost_mono; [| exact (P w PW eq_refl)]; try phi_auto | ]
  end end.
Notation EWORLD := (mkW (mkIS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (mkIC _ _ _ _ _ _ _ _ _ _ _) (mkIR _ _ _ _ _ _ _ _ _)) (only parsing).
Ltac fin_apply lem a1 a2 H1 :=
  let PW := fresh "PW" in let HB := fresh "HB" in let F := fresh "F" in
  let w := open_constr:(mkW (mkIS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (mkIC _ _ _ _ _ _ _ _ _ _ _) (mkIR _ _ _ _ _ _ _ _ _)) in
  eassert (PW : _); [ | eassert (HB : _); [ | pose proof (lem w a1 a2 PW eq_refl H1 HB) as F; wred in F; eapply apost_mono; [| exact F]; try phi_auto ] ].
Ltac fin_apply2 lem a1 a2 H1 :=
  let PW := fresh "PW" in let HB := fresh "HB" in let HB2 := fresh "HB2" in let F := fresh "F" in
  let w := open_constr:(mkW (mkIS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (mkIC _ _ _ _ _ _ _ _ _ _ _) (mkIR _ _ _ _ _ _ _ _ _)) in
  eassert (PW : _); [ | eassert (HB : _); [ | eassert (HB2 : _); [ | pose proof (lem w a1 a2 PW eq_refl H1 HB HB2) as F; wred in F; eapply apost_mono; [| exact F]; try phi_auto ] ] ].
Ltac kinv_close := unfold cinv, cks; cbn [w_s w_c w_r is_mode is_wrap is_flags is_check is_hold is_bits ic_next_out ic_avail_in ic_avail_out
                                             ir_put ir_out ir_left ir_have ir_hold ir_bits].
Ltac pinv_split :=
  unfold InflateInv.pinv; cbn [w_s];
  split; [assumption|]; split; [apply LRNGq_mk; [srng_close | cinv_close | rinv_close | winv_close | cross_close] | split; [| split; [xinv_close | split; [binv_close | kinv_close]]]].
Ltac pinv0_split :=
  unfold InflateInv.pinv0; cbn [w_s];
  split; [assumption|]; split; [apply LRNGq_mk; [srng_close | cinv_close | rinv_close | winv_close | cross_close] | split; [| split; [xinv_close | kinv_close]]].

Lemma wrap64_idem : forall x, wrap64 (wrap64 x) = wrap64 x.
Proof. intros x. apply wrap64_id. apply wrap64_range. Qed.

Lemma wrap64_add_eq : forall a b k, wrap64 a = wrap64 b -> wrap64 (a + k) = wrap64 (b + k).
Proof.
  intros a b k H. rewrite !wrap64_mod in *. rewrite <- (Zplus_mod_idemp_l a), <- (Zplus_mod_idemp_l b). rewrite H. reflexivity.
Qed.

Ltac binv_use :=
  match goal with H : binv _ |- _ => unfold binv in H; cbn [w_s w_r ir_bits ir_hold is_mode] in H; pend_red_in H | _ => idtac end.
Ltac binv_auto :=
  first [ left; glia
        | right; first [exact I | glia | assumption]
        | binv_use; first [ left; glia | right; first [glia | assumption] ]
        | idtac ].
Ltac konly := repeat match goal with H : _ |- _ => clear H end.
Ltac ck_solve :=
  let Hm := fresh "Hm" in let Hw := fresh "Hw" in let Hf := fresh "Hf" in
  intros Hm Hw Hf;
  first [ apply ck_adl_init | apply ck_adl_crc0 | apply ck_adl_upd
        | (apply ck_adl_UPD; first [exact Hf | reflexivity | assumption])
        | (exfalso; clear - Hm; mlia)
        | match reverse goal with Y : _ -> _ -> _ -> ck_adl _ |- _ => apply Y; solve [assumption | (konly; mlia) | (atrim; mlia)] end
        | (exfalso; lazymatch type of Hw with Z.land ?wr _ <> 0 =>
                      match goal with E : wr = _ |- _ => rewrite E in Hw; cbv in Hw; lia end end)
        | (exfalso; lazymatch type of Hf with ?fl = 0 =>
                      match goal with E : fl = _ |- _ => rewrite E in Hf; cbv in Hf; lia end end)
        | (exfalso; clear - Hm Hw Hf; first [(cbv in Hw; lia) | (cbv in Hf; lia)])
        | (exfalso; glia)
        | idtac ].
Ltac kinv_auto :=
  split; [ ck_solve
  | split; [ first [ assumption | (let Hm := fresh in intros Hm; exfalso; clear - Hm; mlia) | (intros; glia) | idtac ]
  | split; [ first [ assumption | (let Hm := fresh in intros Hm; exfalso; clear - Hm; mlia)
                   | (intros; repeat split; first [assumption | reflexivity | glia]) | idtac ]
  | split; [ first [ assumption | ck_solve ]
  | first [ (split; glia) | idtac ] ]]]].
Ltac pinv_auto :=
  pinv_split;
  [ conj_solve | conj_solve | conj_solve
  | first [assumption | (winv_close; conj_solve)]
  | first [assumption | idtac]
  | try sinv_easy
  | try xinv_auto
  | try binv_auto
  | first [assumption | kinv_auto] ].
Ltac pinv0_auto :=
  pinv0_split;
  [ conj_solve | conj_solve | conj_solve
  | first [assumption | (winv_close; conj_solve)]
  | first [assumption | idtac]
  | try sinv_easy
  | try xinv_auto
  | first [assumption | kinv_auto] ].
Ltac arun_post := split; [pinv_auto | try phi_auto].
Ltac bsaved_close := unfold binv_saved; pend_red.
Ltac cks_close := unfold cks; cbn [is_mode is_wrap is_flags is_check]; ck_solve.
Ltac lrng_auto :=
  apply LRNGq_mk; [ first [assumption | (srng_close; conj_solve)] | first [assumption | (cinv_close; conj_solve)]
                  | first [assumption | (match goal with RI : RINV _ _ ?r |- RINV _ _ ?r' => rinv_open RI end; rinv_close; conj_solve) | (rinv_close; conj_solve)]
                  | winv_close; first [assumption | conj_solve] | cross_close; first [assumption | glia | idtac] ].
Ltac leave_post :=
  split; [first [assumption | lrng_auto] |
  split; [first [assumption | sinv_easy]
         | first [ (split; [binv_close; binv_auto | split; [(split; reflexivity) | first [assumption | cks_close]]])
                 | (split; [binv_close; binv_auto | first [assumption | cks_close]]) ] ] ].
Ltac leave_post5 :=
  split; [first [assumption | lrng_auto] |
  split; [first [assumption | sinv_easy]
  | split; [binv_close; binv_auto
  | split; [first [assumption | cks_close]
  | split; [try xinv_auto | kinv_close; kinv_auto]]]] ].
Ltac chain_tail P :=
  eapply apost_mono; [| apply P; [| first [reflexivity | (left; reflexivity) | (right; reflexivity)]]; pinv_auto]; try phi_auto.
Ltac chain_both P :=
  lazymatch goal with |- _ = true /\ _ _ (_ ?wm) =>
    let G := fresh "G" in let A := fresh "A" in
    unshelve epose proof (P wm _ ltac:(first [reflexivity | (left; reflexivity) | (right; reflexivity)])) as [G A];
      [| split; [exact G | eapply apost_mono; [| exact A]; try phi_auto]]; pinv_auto
  end.
Ltac chain_tail2 P :=
  lazymatch goal with |- _ _ (_ ?wm) =>
    let A := fresh "A" in
    eapply apost_mono; [| unshelve epose proof (P wm _ ltac:(first [reflexivity | (left; reflexivity) | (right; reflexivity)])) as [_ A]; [| exact A]; pinv_auto]; try phi_auto
  end.


Definition plain_mode (m : Z) : Prop :=
  codes_live m = false /\ m <> LENLENS /\ m <> CODELENS /\ m <> LENEXT /\ m <> DIST /\ m <> DISTEXT /\ m <> MATCH /\ m <> COPY_ /\ m <> COPY.

Lemma sinv_plain : forall s m, sinv s -> plain_mode m -> sinv (iset_mode s m).
Proof.
  intros s m SI (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). destruct SI as (W1 & W2 & AL & _). destruct s.
  unfold sinv in *. cbn -[Z.shiftl tables_ok ctab_ok tables_rep ctab_rep arr_get] in *. rewrite P0. split; [exact W1|]. split; [exact W2|]. split; [exact AL|].
  repeat match goal with |- _ /\ _ => split end; intros; try (exfalso; mlia); try discriminate; mlia.
Qed.

Lemma plain_modes : plain_mode HEAD /\ plain_mode FLAGS /\ plain_mode TIME /\ plain_mode OS /\ plain_mode EXLEN
  /\ plain_mode EXTRA /\ plain_mode NAME /\ plain_mode COMMENT /\ plain_mode HCRC /\ plain_mode DICTID /\ plain_mode DICT
  /\ plain_mode TYPE /\ plain_mode TYPEDO /\ plain_mode STORED /\ plain_mode TABLE /\ plain_mode CHECK /\ plain_mode LENGTH
  /\ plain_mode DONE /\ plain_mode BAD /\ plain_mode MEM /\ plain_mode SYNC.
Proof. unfold plain_mode; repeat split; try reflexivity; discriminate. Qed.

Lemma sinv_to_LEN : forall s, sinv s -> codes_live (is_mode s) = true -> sinv (iset_mode s LEN).
Proof.
  intros s SI L. destruct SI as (W1 & W2 & AL & T & _ & _ & _ & _ & _ & _ & _ & TR & _). specialize (T L). specialize (TR L). destruct s.
  unfold sinv, tables_ok, tables_rep in *. cbn -[Z.shiftl tables_okf ctab_ok rep_ok ctab_rep cat arr_get arr_len] in *. split; [exact W1|]. split; [exact W2|]. split; [exact AL|].
  split; [intros _; exact T|].
  repeat match goal with |- _ /\ _ => split end; intros; try (exfalso; mlia); try exact TR; try (destruct TR; assumption); mlia.
Qed.

