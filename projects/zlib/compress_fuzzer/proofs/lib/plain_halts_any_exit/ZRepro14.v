(** * ZRepro14 — zlib 1.4 twins of ZRepro's two inflate entry points.

     ruling (A): RT's inflate gets a 1.4 flavour ([Spec.PngModel.Inflate14]) and the 1.3.1 texts stay
    unchanged.  [zr_inf_call14] / [zr_inflate14] are [ZRepro.zr_inf_call] / [ZRepro.zr_inflate] word for word,
    with [Inflate14.inflate_model14] for [Inflate.inflate_model].  [inflateInit2] is RT's 1.3.1 one: on the fresh
    state the harness passes, zlib 1.4's init (zmemzero, reqwrap / reqbits, the window freed only on a wbits
    change) yields the same state.  Not modelled in the 1.4 flavour, and not visible here: 1.4's DICT arm adds
    [in - avail_in] to total_in before returning Z_NEED_DICT; [zr_inflate14] reads only the bytes of a
    Z_STREAM_END return. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel
  Require Import Base Checksum Chunk ZBitsIn ZBitsOut InflateFast Inflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Inflate14.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** [ZRepro.zr_inf_call] at 1.4. Returns (code, consumed, state', strm', produced bytes). *)
Definition zr_inf_call14 (flush : Z) (s : IState) (z : Strm) (inb : list Z)
                         (avail_out : Z)
  : option (Z * Z * IState * Strm * list Z) :=
  match Inflate14.inflate_model14
          {| g_st := s; g_state_null := false; g_z := z;
             g_inbuf := zlist inb; g_next_in := 0;
             g_avail_in := zlen inb; g_in_null := false;
             g_outbuf := zzero; g_next_out := 0;
             g_avail_out := avail_out; g_out_null := false;
             g_flush := flush; g_walloc := true;
             g_wfresh := zzero |} with
  | None => None
  | Some r =>
      let q := r_q r in
      Some (r_ret r, zlen inb - br_have (q_br q),
            q_st q, q_z q, ob_slice (q_ob q) 0 (o_put (q_ob q)))
  end.

(** [ZRepro.zr_inflate] at 1.4: one inflate call over the whole stream, [Some] only at [Z_STREAM_END]. *)
Definition zr_inflate14 (flush windowBits cap : Z) (enc : list Z)
  : option (list Z) :=
  match inflateInit2 z_fresh state_fresh windowBits with
  | None => None
  | Some (z, s) =>
      match zr_inf_call14 flush s z enc cap with
      | None => None
      | Some (ret, _, _, _, out) =>
          if Z.eqb ret Z_STREAM_END then Some out else None
      end
  end.
