(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarb
  InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateIeq.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac dstate2 s :=
  destruct s as [g_mode g_last g_wrap g_havedict g_flags g_dmax g_check g_total g_head g_wbits g_wsize g_whave g_wnext
                 g_window g_window_blk g_hold g_bits g_length g_offset g_extra g_lencode g_distcode g_lenbits g_distbits
                 g_ncode g_nlen g_ndist g_have g_next g_lens g_work g_codes g_sane g_back g_was g_self_blk].
Ltac dstate1 s :=
  destruct s as [f_mode f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                 f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                 f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk].
Ltac dstate1x s :=
  destruct s as [x_mode x_last x_wrap x_havedict x_flags x_dmax x_check x_total x_head x_wbits x_wsize x_whave x_wnext
                 x_window x_window_blk x_hold x_bits x_length x_offset x_extra x_lencode x_distcode x_lenbits x_distbits
                 x_ncode x_nlen x_ndist x_have x_next x_lens x_work x_codes x_sane x_back x_was x_self_blk].
Ltac dstate2x s :=
  destruct s as [y_mode y_last y_wrap y_havedict y_flags y_dmax y_check y_total y_head y_wbits y_wsize y_whave y_wnext
                 y_window y_window_blk y_hold y_bits y_length y_offset y_extra y_lencode y_distcode y_lenbits y_distbits
                 y_ncode y_nlen y_ndist y_have y_next y_lens y_work y_codes y_sane y_back y_was y_self_blk].
Ltac dcallx c := destruct c as [d_input d_next_in d_avail_in d_outbuf d_next_out d_avail_out d_total_in d_total_out d_adler d_data_type d_msg].
Ltac dregsx r := destruct r as [q_next q_have q_put q_left q_hold q_bits q_in q_out q_ref].
Ltac cdt_red := cbv beta iota delta [cdt icset_data_type ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out
                                     ic_total_in ic_total_out ic_adler ic_data_type ic_msg].
Ltac cdt_red_in H := cbv beta iota delta [cdt icset_data_type ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out
                                     ic_total_in ic_total_out ic_adler ic_data_type ic_msg] in H.
Ltac dcall c := destruct c as [c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg].
Ltac dregs r := destruct r as [r_next r_have r_put r_left r_hold r_bits r_in r_out r_ref].

Ltac proj_cbn_in H :=
  cbn [w_s w_c w_r is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in H.

Ltac live_red_in H :=
  cbv beta iota zeta delta [live_check live_length live_offset live_extra live_lenbits live_distbits live_dyn live_codes codes_live chk_guard
       is_mode is_wrap is_flags ir_out ir_left
       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE
       LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in H;
  cbn [andb orb negb xorb Z.eqb Z.ltb Z.leb Z.compare Pos.compare Pos.compare_cont Pos.eqb] in H.
Ltac live_red :=
  cbv beta iota zeta delta [live_check live_length live_offset live_extra live_lenbits live_distbits live_dyn live_codes codes_live chk_guard
       is_mode is_wrap is_flags ir_out ir_left
       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE
       LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC];
  cbn [andb orb negb xorb Z.eqb Z.ltb Z.leb Z.compare Pos.compare Pos.compare_cont Pos.eqb].

Ltac clause1 H :=
  live_red_in H;
  first [ match type of H with
          | true = true -> ?g = _ => specialize (H eq_refl); first [subst g | idtac]
          | false = true -> _ => clear H
          | ?m = ?m -> _ => specialize (H eq_refl)
          | ?m = ?m' -> _ =>
              let X := fresh in assert (X : m <> m') by (clear; discriminate); clear X H
          | _ => idtac
          end
        | idtac ].

Ltac seq_open SQ :=
  unfold SEQX, icoreq in SQ; proj_cbn_in SQ;
  destruct SQ as (CORE & CK & LEN & OFS & EXT & LB & DB & DYN & ALl & ALw & ALc & ALn & LL & CL & CO & WIq & WW);
  injection CORE; clear CORE;
  intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->;
  clause1 LEN; clause1 OFS; clause1 EXT; clause1 LB; clause1 DB;
  live_red_in DYN;
  first [ match type of DYN with
          | true = true -> _ => destruct (DYN eq_refl) as (-> & -> & -> & ->); clear DYN
          | false = true -> _ => clear DYN
          end | idtac ];
  live_red_in LL; first [ specialize (LL eq_refl) | clear LL | idtac ];
  live_red_in CL; first [ specialize (CL eq_refl) | clear CL | idtac ];
  live_red_in CO;
  first [ match type of CO with true = true -> _ => specialize (CO eq_refl) | false = true -> _ => clear CO end | idtac ];
  live_red_in CK;
  first [ match type of CK with true = true -> ?g = _ => specialize (CK eq_refl); subst g end | idtac ].

Ltac seq_open_keep SQ :=
  unfold SEQX, icoreq in SQ; proj_cbn_in SQ;
  destruct SQ as (CORE & CK & LEN & OFS & EXT & LB & DB & DYN & ALl & ALw & ALc & ALn & LL & CL & CO & WIq & WW);
  injection CORE; clear CORE;
  intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->.

Ltac seqx_split :=
  unfold SEQX, icoreq;
  cbn [w_s w_c w_r is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk];
  split; [reflexivity|];
  repeat match goal with |- _ /\ _ => split end.
Ltac weq_split :=
  lazymatch goal with
  | |- RREL (ARun _ _) (ARun _ _) => cbn [RREL]; split; [reflexivity|]
  | |- RREL (ALeave _) (ALeave _) => cbn [RREL]
  | |- RREL (ARet _ _) (ARet _ _) => cbn [RREL]; split; [reflexivity|]
  | |- WEQ _ _ => idtac
  | |- SEQX _ _ _ => idtac
  end;
  lazymatch goal with
  | |- WEQ _ _ => unfold WEQ; cbn [w_c w_r w_s]; split;
      [ cbv beta iota delta [cdt icset_data_type ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out
                             ic_total_in ic_total_out ic_adler ic_data_type ic_msg]; reflexivity
      | split; [reflexivity|] ]
  | |- _ => idtac
  end;
  seqx_split.

Ltac guard_from K :=
  let X := fresh "X" in
  intros X; apply K; revert X; live_red;
  repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end;
  cbv beta iota delta [andb orb negb]; intros; first [reflexivity | assumption | discriminate].

Ltac liaq_noback := first [ solve [liaq_prune_logic; liaq_prune_nl; lia] | solve [liaq_prune_logic; lia] ].
Ltac weq_clause :=
  first [ reflexivity
        | assumption
        | (live_red;
           lazymatch goal with
           | |- false = true -> _ => let X := fresh in intros X; discriminate X
           | |- _ = true -> ?a = ?a => intros _; reflexivity
           | |- _ -> ?a = ?a /\ _ => intros _; repeat split; reflexivity
           | |- _ -> ?g = ?f =>
               first [ assumption
                     | match goal with K : _ -> g = f |- _ => guard_from K end
                     | (let X := fresh in intros X;
                        first [assumption | reflexivity | (exfalso; clear - X; discriminate X)]) ]
           | |- _ -> forall i, _ =>
               first [ assumption
                     | (let X := fresh in intros X;
                        first [assumption | (exfalso; clear - X; discriminate X) | (intros; liaq_noback)]) ]
           | |- _ -> _ => first [ assumption
                                | (let X := fresh in intros X;
                                   first [assumption | reflexivity | (exfalso; clear - X; discriminate X)]) ]
           | |- _ => first [assumption | reflexivity]
           end) ].
Ltac weq_auto := weq_split; try weq_clause.

Ltac chain I := apply I; [reflexivity | weq_auto].

Ltac nb_sync :=
  lazymatch goal with |- RREL ?A ?B =>
    match A with context [NEEDBITS ?n (mkW ?s1 ?c ?r)] =>
    match B with context [NEEDBITS n (mkW ?s2 ?c2 r)] =>
      let E := fresh "E" in let K := fresh "Knb" in
      pose proof (NEEDBITS_free n s1 s2 c c2 r ltac:(reflexivity)) as [E K]; rewrite E; clear E K
    end end
  end.
Ltac nb_step :=
  lazymatch goal with |- RREL ?A ?B =>
    match A with context [NEEDBITS ?n (mkW ?s1 ?c ?r)] =>
    match B with context [NEEDBITS n (mkW ?s2 ?c2 r)] =>
      let E := fresh "E" in let K := fresh "K" in let r1 := fresh "r" in
      let n1 := fresh "n" in let h1 := fresh "hv" in let p1 := fresh "p" in let l1 := fresh "l" in
      let ho1 := fresh "ho" in let b1 := fresh "b" in let i1 := fresh "i" in let o1 := fresh "o" in let rt1 := fresh "rt" in
      pose proof (NEEDBITS_free n s1 s2 c c2 r ltac:(reflexivity)) as [E K]; rewrite E; clear E;
      destruct (NEEDBITS n (mkW s1 c r)) as [[] ?|?|? ?];
      destruct K as (r1 & -> & K); destruct r1 as [n1 h1 p1 l1 ho1 b1 i1 o1 rt1];
      cbv beta iota delta [keep5 ir_put ir_left ir_in ir_out ir_ret] in K;
      destruct K as (-> & -> & -> & -> & ->);
      cbv beta iota delta [reput w_r]
    end end
  end.
Ltac nb := nb_step; [ wred | weq_auto | weq_auto ].

Ltac dc_step hc :=
  lazymatch goal with |- RREL ?A ?B =>
    match A with context [DECODE_k ?k ?p ?ix ?nd (mkW ?s1 ?c ?r)] =>
    match B with context [DECODE_k k p ix nd (mkW ?s2 ?c2 r)] =>
      let E := fresh "E" in let K := fresh "K" in let HC := fresh "HC" in let r1 := fresh "r" in
      let hq := fresh "hq" in let Hhere := fresh "Hhere" in let here := fresh "here" in
      let n1 := fresh "n" in let h1 := fresh "hv" in let p1 := fresh "p" in let l1 := fresh "l" in
      let ho1 := fresh "ho" in let b1 := fresh "b" in let i1 := fresh "i" in let o1 := fresh "o" in let rt1 := fresh "rt" in
      assert (HC : forall h, code_at s2 p (ix h) = code_at s1 p (ix h));
      [ hc
      | pose proof (DECODE_k_par k p ix nd s1 s2 c c2 r ltac:(reflexivity) HC) as [E K]; rewrite E; clear E;
        destruct (DECODE_k k p ix nd (mkW s1 c r)) as [here ?|?|? ?];
        [ destruct K as (hq & r1 & Hhere & -> & K) | destruct K as (r1 & -> & K) | destruct K as (r1 & -> & K) ];
        destruct r1 as [n1 h1 p1 l1 ho1 b1 i1 o1 rt1];
        cbv beta iota delta [keep5 ir_put ir_left ir_in ir_out ir_ret] in K;
        destruct K as (-> & -> & -> & -> & ->);
        cbv beta iota delta [reput w_r] ]
    end end
  end.
Ltac dc hc := dc_step hc; [ wred | weq_auto | weq_auto ].

Ltac reput_red := cbv beta iota delta [reput w_r].
