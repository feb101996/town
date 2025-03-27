import { alloc_tensor } from '../runtime/alloc';
import {
  caddr,
  cadr,
  car,
  Constants,
  DEBUG,
  defs,
  ismultiply,
  ispower,
  NIL,
  SECRETX,
  SETQ,
  Tensor,
  TESTEQ,
  U
} from '../runtime/defs';
import { stop } from '../runtime/run';
import { symbol } from "../runtime/symbol";
import { cmp_expr, sort } from '../sources/misc';
import { absValFloat } from './abs';
import { add, add_all, subtract } from './add';
import { integer, rational } from './bignum';
import { coeff } from './coeff';
import { Eval } from './eval';
import { factorpoly } from './factorpoly';
import { guess } from './guess';
import { iscomplexnumber, ispolyexpandedform, isposint, isZeroAtomOrTensor } from './is';
import { divide, multiply, negate } from './multiply';
import { power } from './power';
import { simplify } from './simplify';

var log = {
  debug: (str: string) => {
    if (DEBUG) {
      console.log(str);
    }
  },
};

var flatten = (arr: any[]) => [].concat(...arr);

//define POLY p1
//define X p2
//define A p3
//define B p4
//define C p5
//define Y p6

export function Eval_roots(POLY: U) {
  // A == B -> A - B
  let X = cadr(POLY);
  let POLY1: U;
  if (car(X) === symbol(SETQ) || car(X) === symbol(TESTEQ)) {
    POLY1 = subtract(Eval(cadr(X)), Eval(caddr(X)));
  } else {
    X = Eval(X);
    if (car(X) === symbol(SETQ) || car(X) === symbol(TESTEQ)) {
      POLY1 = subtract(Eval(cadr(X)), Eval(caddr(X)));
    } else {
      POLY1 = X;
    }
  }

  // 2nd arg, x
  X = Eval(caddr(POLY));

  var X1 = X === symbol(NIL) ? guess(POLY1) : X;

  if (!ispolyexpandedform(POLY1, X1)) {
    stop('roots: 1st argument is not a polynomial in the variable ' + X1);
  }

  return roots(POLY1, X1);
}

function hasImaginaryCoeff(k: U[]): boolean {
  return k.some((c) => iscomplexnumber(c));
}

// k[0]      Coefficient of x^0
// k[n-1]    Coefficient of x^(n-1)
function isSimpleRoot(k: U[]): boolean {
  if (k.length <= 2) {
    return false;
  }
    if (isZeroAtomOrTensor(k[0])) {
    return false;
  }
  return k.slice(1, k.length - 1).every((el) => isZeroAtomOrTensor(el));
}

function normalisedCoeff(poly: U, x: U): U[] {
  var miniStack = coeff(poly, x);
  var divideBy = miniStack[miniStack.length - 1];
  return miniStack.map((item) => divide(item, divideBy));
}

export function roots(POLY: U, X: U): U {
  // the simplification of nested radicals uses "roots", which in turn uses
  // simplification of nested radicals. Usually there is no problem, one level
  // of recursion does the job. Beyond that, we probably got stuck in a
  // strange case of infinite recursion, so bail out and return NIL.
  if (defs.recursionLevelNestedRadicalsRemoval > 1) {
    return symbol(NIL);
  }

  log.debug(`checking if ${POLY} is a case of simple roots`);

  var k = normalisedCoeff(POLY, X);

  var results = [];
  if (isSimpleRoot(k)) {
    log.debug(`yes, ${k[k.length - 1]} is a case of simple roots`);
    var kn = k.length;
    var lastCoeff = k[0];
    var leadingCoeff = k.pop();
    var simpleRoots = getSimpleRoots(kn, leadingCoeff, lastCoeff);
    results.push(...simpleRoots);
  } else {
    var roots = roots2(POLY, X);
    results.push(...roots);
  }

  var n = results.length;
  if (n === 0) {
    stop('roots: the polynomial is not factorable, try nroots');
  }
  if (n === 1) {
    return results[0];
  }
  sort(results);
  var tensor = alloc_tensor(n);
  tensor.tensor.ndim = 1;
  tensor.tensor.dim[0] = n;
  for (let i = 0; i < n; i++) {
    tensor.tensor.elem[i] = results[i];
  }
  console.log(`roots returning ${tensor}`);
  return tensor;
}

// ok to generate these roots take a look at their form
// in the case of even and odd exponents here:
// http://www.wolframalpha.com/input/?i=roots+x%5E14+%2B+1
// http://www.wolframalpha.com/input/?i=roots+ax%5E14+%2B+b
// http://www.wolframalpha.com/input/?i=roots+x%5E15+%2B+1
// http://www.wolframalpha.com/input/?i=roots+a*x%5E15+%2B+b
// leadingCoeff    Coefficient of x^0
// lastCoeff       Coefficient of x^(n-1)
function getSimpleRoots(n: number, leadingCoeff: U, lastCoeff: U):U[] {
  log.debug('getSimpleRoots');

  n = n - 1;

  var commonPart = divide(
    power(lastCoeff, rational(1, n)),
    power(leadingCoeff, rational(1, n))
  );
  var results = [];

  if (n % 2 === 0) {
    for (let i = 1; i <= n; i += 2) {
      var aSol = multiply(
        commonPart,
        power(Constants.negOne, rational(i, n))
      );
      results.push(aSol);
      results.push(negate(aSol));
    }
    return results;
  }

  for (let i = 1; i <= n; i++) {
    let sol = multiply(commonPart, power(Constants.negOne, rational(i, n)));
    if (i % 2 === 0) {
      sol = negate(sol);
    }
    results.push(sol);
  }
  return results;
}

function roots2(POLY: U, X: U): U[] {
  var k = normalisedCoeff(POLY, X);
  if (!hasImaginaryCoeff(k)) {
    POLY = factorpoly(POLY, X);
  }
  if (ismultiply(POLY)) {
    // scan through all the factors and find the roots of each of them
    var mapped = POLY.tail().map((p) => roots3(p, X));
    return flatten(mapped);
  }
  return roots3(POLY, X);
}

function roots3(POLY: U, X: U): U[] {
  if (
    ispower(POLY) &&
    ispolyexpandedform(cadr(POLY), X) &&
    isposint(caddr(POLY))
  ) {
    var n = normalisedCoeff(cadr(POLY), X);
    return mini_solve(n);
  }
  if (ispolyexpandedform(POLY, X)) {
    var n = normalisedCoeff(POLY, X);
    return mini_solve(n);
  }
  return [];
}

// note that for many quadratic, cubic and quartic polynomials we don't
// actually end up using the quadratic/cubic/quartic formulas in here,
// since there is a chance we factored the polynomial and in so
// doing we found some solutions and lowered the degree.
function mini_solve(coefficients: U[]):U[] {
  var n = coefficients.length;

  // AX + B, X = -B/A
  if (n === 2) {
    var A = coefficients.pop();
    var B = coefficients.pop();
    return _solveDegree1(A, B);
  }

  // AX^2 + BX + C, X = (-B +/- (B^2 - 4AC)^(1/2)) / (2A)
  if (n === 3) {
    var A = coefficients.pop();
    var B = coefficients.pop();
    var C = coefficients.pop();
    return _solveDegree2(A, B, C);
  }

  if (n === 4) {
    var A = coefficients.pop();
    var B = coefficients.pop();
    var C = coefficients.pop();
    var D = coefficients.pop();
    return _solveDegree3(A, B, C, D);
  }

  // See http://www.sscc.edu/home/jdavidso/Math/Catalog/Polynomials/Fourth/Fourth.html
  // for a description of general shapes and properties of fourth degree polynomials
  if (n === 5) {
    var A = coefficients.pop();
    var B = coefficients.pop();
    var C = coefficients.pop();
    var D = coefficients.pop();
    var E = coefficients.pop();
    return _solveDegree4(A, B, C, D, E);
  }

  return [];
}

function _solveDegree1(A: U, B: U): U[] {
  return [negate(divide(B, A))];
}

function _solveDegree2(A: U, B: U, C: U): U[] {
    //(B^2 - 4AC)^(1/2)
  var p6 = power(
    // prettier-ignore
    subtract(
        power(B, integer(2)), 
        multiply(multiply(integer(4), A), C)
      ),
    rational(1, 2)
  );

  // ((B^2 - 4AC)^(1/2) - B)/ (2A)
  var result1 = divide(subtract(p6, B), multiply(A, integer(2)));

  // 1/2 * -(B + (B^2 - 4AC)^(1/2)) / A
  var result2 = multiply(divide(negate(add(p6, B)), A), rational(1, 2));
  return [result1, result2];
  }

function _solveDegree3(A: U, B: U, C: U, D: U): U[] {
    // C - only related calculations
  var R_c3 = multiply(multiply(C, C), C);

    // B - only related calculations
  var R_b2 = multiply(B, B);

  var R_b3 = multiply(R_b2, B);

  var R_m4_b3_d = multiply(multiply(R_b3, D), integer(-4));

    var R_2_b3 = multiply(R_b3, integer(2));

    // A - only related calculations
  var R_3_a = multiply(integer(3), A);

  var R_a2_d = multiply(multiply(A, A), D);

    var R_27_a2_d = multiply(R_a2_d, integer(27));

  var R_m27_a2_d2 = multiply(multiply(R_a2_d, D), integer(-27));

    // mixed calculations
  var R_a_b_c = multiply(multiply(A, C), B);

  var R_3_a_c = multiply(multiply(A, C), integer(3));

  var R_m4_a_c3 = multiply(integer(-4), multiply(A, R_c3));

    var R_m9_a_b_c = negate(multiply(R_a_b_c, integer(9)));

  var R_18_a_b_c_d = multiply(multiply(R_a_b_c, D), integer(18));

  var R_DELTA0 = subtract(R_b2, R_3_a_c);

  var R_b2_c2 = multiply(R_b2, multiply(C, C));

  var R_m_b_over_3a = divide(negate(B), R_3_a);

      var R_4_DELTA03 = multiply(power(R_DELTA0, integer(3)), integer(4));

      var R_DELTA0_toBeCheckedIfZero = absValFloat(simplify(R_DELTA0));

  var R_determinant = absValFloat(
        simplify(
          add_all([R_18_a_b_c_d, R_m4_b3_d, R_b2_c2, R_m4_a_c3, R_m27_a2_d2])
        )
      );
  var R_DELTA1 = add_all([R_2_b3, R_m9_a_b_c, R_27_a2_d]);
  var R_Q = simplify(
    power(subtract(power(R_DELTA1, integer(2)), R_4_DELTA03), rational(1, 2))
      );

  log.debug('>>>>>>>>>>>>>>>> actually using cubic formula <<<<<<<<<<<<<<< ');
  log.debug(`cubic: D0: ${R_DELTA0}`);
  log.debug(`cubic: D0 as float: ${R_DELTA0_toBeCheckedIfZero}`);
  log.debug(`cubic: DETERMINANT: ${R_determinant}`);
  log.debug(`cubic: D1: ${R_DELTA1}`);

      if (isZeroAtomOrTensor(R_determinant)) {
    var data = {
      R_DELTA0_toBeCheckedIfZero,
      R_m_b_over_3a,
      R_DELTA0,
      R_b3,
      R_a_b_c,
    };
    return _solveDegree3ZeroRDeterminant(A, B, C, D, data);
      }

      let C_CHECKED_AS_NOT_ZERO = false;
      let flipSignOFQSoCIsNotZero = false;

  let R_C: U;
  // C will go as denominator, we have to check that is not zero
      while (!C_CHECKED_AS_NOT_ZERO) {
    var arg1 = flipSignOFQSoCIsNotZero ? negate(R_Q) : R_Q;
        R_C = simplify(
          power(multiply(add(arg1, R_DELTA1), rational(1, 2)), rational(1, 3))
        );
        var R_C_simplified_toCheckIfZero = absValFloat(simplify(R_C));

    log.debug(`cubic: C: ${R_C}`);
    log.debug(`cubic: C as absval and float: ${R_C_simplified_toCheckIfZero}`);

        if (isZeroAtomOrTensor(R_C_simplified_toCheckIfZero)) {
      log.debug(' cubic: C IS ZERO flipping the sign');
          flipSignOFQSoCIsNotZero = true;
        } else {
          C_CHECKED_AS_NOT_ZERO = true;
        }
      }

  var R_6_a_C = multiply(multiply(R_C, R_3_a), integer(2));

      // imaginary parts calculations
      var i_sqrt3 = multiply(
        Constants.imaginaryunit,
        power(integer(3), rational(1, 2))
      );
      var one_plus_i_sqrt3 = add(Constants.one, i_sqrt3);
      var one_minus_i_sqrt3 = subtract(Constants.one, i_sqrt3);
      var R_C_over_3a = divide(R_C, R_3_a);

      // first solution
  var firstSolTerm1 = R_m_b_over_3a;
  var firstSolTerm2 = negate(R_C_over_3a);
  var firstSolTerm3 = negate(divide(R_DELTA0, multiply(R_C, R_3_a)));
  var firstSolution = simplify(
    add_all([firstSolTerm1, firstSolTerm2, firstSolTerm3])
  );

      // second solution
  var secondSolTerm1 = R_m_b_over_3a;
      var secondSolTerm2 = divide(
        multiply(R_C_over_3a, one_plus_i_sqrt3),
        integer(2)
  );
  var secondSolTerm3 = divide(multiply(one_minus_i_sqrt3, R_DELTA0), R_6_a_C);
  var secondSolution = simplify(
    add_all([secondSolTerm1, secondSolTerm2, secondSolTerm3])
  );

      // third solution
  var thirdSolTerm1 = R_m_b_over_3a;
      var thirdSolTerm2 = divide(
        multiply(R_C_over_3a, one_minus_i_sqrt3),
        integer(2)
  );
  var thirdSolTerm3 = divide(multiply(one_plus_i_sqrt3, R_DELTA0), R_6_a_C);
  var thirdSolution = simplify(
    add_all([thirdSolTerm1, thirdSolTerm2, thirdSolTerm3])
  );

  return [firstSolution, secondSolution, thirdSolution];
}

interface CommonArgs4ZeroRDeterminant {
  R_DELTA0_toBeCheckedIfZero: U;
  R_m_b_over_3a: U;
  R_DELTA0: U;
  R_b3: U;
  R_a_b_c: U;
}

function _solveDegree3ZeroRDeterminant(
  A: U,
  B: U,
  C: U,
  D: U,
  common: CommonArgs4ZeroRDeterminant
): U[] {
  var {
    R_DELTA0_toBeCheckedIfZero,
    R_m_b_over_3a,
    R_DELTA0,
    R_b3,
    R_a_b_c,
  } = common;
  if (isZeroAtomOrTensor(R_DELTA0_toBeCheckedIfZero)) {
    log.debug(' cubic: DETERMINANT IS ZERO and delta0 is zero');
    return [R_m_b_over_3a]; // just same solution three times
  }
  log.debug(' cubic: DETERMINANT IS ZERO and delta0 is not zero');

  var rootSolution = divide(
    subtract(multiply(A, multiply(D, integer(9))), multiply(B, C)),
    multiply(R_DELTA0, integer(2))
  );

  // second solution here

  // -9*b^3
  var numer_term1 = negate(R_b3);
  // -9a*a*d
  var numer_term2 = negate(multiply(A, multiply(A, multiply(D, integer(9)))));
  // 4*a*b*c
  var numer_term3 = multiply(R_a_b_c, integer(4));

  // build the fraction
  // numerator: sum the three terms
  // denominator: a*delta0
  var secondSolution = divide(
    add_all([numer_term3, numer_term2, numer_term1]),
    multiply(A, R_DELTA0)
  );

  return [rootSolution, rootSolution, secondSolution];
}

function _solveDegree4(A: U, B: U, C: U, D: U, E: U): U[] {
  log.debug('>>>>>>>>>>>>>>>> actually using quartic formula <<<<<<<<<<<<<<< ');

      if (
    isZeroAtomOrTensor(B) &&
    isZeroAtomOrTensor(D) &&
    !isZeroAtomOrTensor(C) &&
    !isZeroAtomOrTensor(E)
      ) {
    return _solveDegree4Biquadratic(A, B, C, D, E);
        }

  if (!isZeroAtomOrTensor(B)) {
    return _solveDegree4NonzeroB(A, B, C, D, E);
      } else {
    return _solveDegree4ZeroB(A, B, C, D, E);
  }
}

function _solveDegree4Biquadratic(A: U, B: U, C: U, D: U, E: U): U[] {
  log.debug('biquadratic case');

  var biquadraticSolutions = roots(
    add(
      multiply(A, power(symbol(SECRETX), integer(2))),
      add(multiply(C, symbol(SECRETX)), E)
    ),
    symbol(SECRETX)
  ) as Tensor;

  var results = [];
  for (var sol of biquadraticSolutions.tensor.elem) {
    results.push(simplify(power(sol, rational(1, 2))));
    results.push(simplify(negate(power(sol, rational(1, 2)))));
  }

  return results;
}

function _solveDegree4ZeroB(A: U, B: U, C: U, D: U, E: U): U[] {
  var R_p = C;
  var R_q = D;
  var R_r = E;

        // Ferrari's solution
        // https://en.wikipedia.org/wiki/Quartic_function#Ferrari.27s_solution
        // finding the "m" in the depressed equation
        var coeff2 = multiply(rational(5, 2), R_p);
  var coeff3 = subtract(multiply(integer(2), power(R_p, integer(2))), R_r);
        var coeff4 = add(
          multiply(rational(-1, 2), multiply(R_p, R_r)),
          add(
            divide(power(R_p, integer(3)), integer(2)),
            multiply(rational(-1, 8), power(R_q, integer(2)))
          )
        );

  var arg1 = add(
            power(symbol(SECRETX), integer(3)),
            add(
              multiply(coeff2, power(symbol(SECRETX), integer(2))),
              add(multiply(coeff3, symbol(SECRETX)), coeff4)
            )
          );

  log.debug(`resolventCubic: ${arg1}`);

  var resolventCubicSolutions = roots(arg1, symbol(SECRETX)) as Tensor;
  log.debug(`resolventCubicSolutions: ${resolventCubicSolutions}`);

        let R_m = null;
        //R_m = resolventCubicSolutions.tensor.elem[1]
  for (var sol of resolventCubicSolutions.tensor.elem) {
    log.debug(`examining solution: ${sol}`);

    var toBeCheckedIfZero = absValFloat(add(multiply(sol, integer(2)), R_p));
    log.debug(`abs value is: ${sol}`);

    if (!isZeroAtomOrTensor(toBeCheckedIfZero)) {
      R_m = sol;
            break;
          }
        }

  log.debug(`chosen solution: ${R_m}`);

        var sqrtPPlus2M = simplify(
          power(add(multiply(R_m, integer(2)), R_p), rational(1, 2))
        );

  var twoQOversqrtPPlus2M = simplify(
          divide(multiply(R_q, integer(2)), sqrtPPlus2M)
        );

  var threePPlus2M = add(
          multiply(R_p, integer(3)),
          multiply(R_m, integer(2))
        );

        // solution1
  var sol1Arg = simplify(
    power(negate(add(threePPlus2M, twoQOversqrtPPlus2M)), rational(1, 2))
        );
  var solution1 = divide(add(sqrtPPlus2M, sol1Arg), integer(2));

        // solution2
  var sol2Arg = simplify(
    power(negate(add(threePPlus2M, twoQOversqrtPPlus2M)), rational(1, 2))
        );
  var solution2 = divide(subtract(sqrtPPlus2M, sol2Arg), integer(2));

        // solution3
  var sol3Arg = simplify(
    power(negate(subtract(threePPlus2M, twoQOversqrtPPlus2M)), rational(1, 2))
        );
  var solution3 = divide(add(negate(sqrtPPlus2M), sol3Arg), integer(2));

        // solution4
  var sol4Arg = simplify(
    power(negate(subtract(threePPlus2M, twoQOversqrtPPlus2M)), rational(1, 2))
        );
  var solution4 = divide(subtract(negate(sqrtPPlus2M), sol4Arg), integer(2));

  return [solution1, solution2, solution3, solution4];
  }

function _solveDegree4NonzeroB(A: U, B: U, C: U, D: U, E: U): U[] {
  var R_p = divide(
    add(
      multiply(integer(8), multiply(C, A)),
      multiply(integer(-3), power(B, integer(2)))
    ),
    multiply(integer(8), power(A, integer(2)))
  );
  var R_q = divide(
    add(
      power(B, integer(3)),
      add(
        multiply(integer(-4), multiply(A, multiply(B, C))),
        multiply(integer(8), multiply(D, power(A, integer(2))))
      )
    ),
    multiply(integer(8), power(A, integer(3)))
  );
  var R_a3 = multiply(multiply(A, A), A);
  var R_b2 = multiply(B, B);
  var R_a2_d = multiply(multiply(A, A), D);

  // convert to depressed quartic
  let R_r = divide(
    add(
      multiply(power(B, integer(4)), integer(-3)),
      add(
        multiply(integer(256), multiply(R_a3, E)),
        add(
          multiply(integer(-64), multiply(R_a2_d, B)),
          multiply(integer(16), multiply(R_b2, multiply(A, C)))
        )
      )
    ),
    multiply(integer(256), power(A, integer(4)))
  );
  var four_x_4 = power(symbol(SECRETX), integer(4));
  var r_q_x_2 = multiply(R_p, power(symbol(SECRETX), integer(2)));
  var r_q_x = multiply(R_q, symbol(SECRETX));
  var simplified = simplify(add_all([four_x_4, r_q_x_2, r_q_x, R_r]));
  var depressedSolutions = roots(simplified, symbol(SECRETX)) as Tensor;

  log.debug(`p for depressed quartic: ${R_p}`);
  log.debug(`q for depressed quartic: ${R_q}`);
  log.debug(`r for depressed quartic: ${R_r}`);
  log.debug(`4 * x^4: ${four_x_4}`);
  log.debug(`R_p * x^2: ${r_q_x_2}`);
  log.debug(`R_q * x: ${r_q_x}`);
  log.debug(`R_r: ${R_r}`);
  log.debug(`solving depressed quartic: ${simplified}`);
  log.debug(`depressedSolutions: ${depressedSolutions}`);

  return depressedSolutions.tensor.elem.map((sol) => {
    var result = simplify(subtract(sol, divide(B, multiply(integer(4), A))));
    log.debug(`solution from depressed: ${result}`);
    return result;
  });
}
