#include <stdio.h>//стандартная библиотека для ввода-вывода в Си
#include <stdlib.h>
#include <math.h>// библиотека для разных мат.функций


constexpr auto delta = 1.e-5;// 
constexpr auto N = 2;// размер массива куда запишутся фазовые переменые
constexpr auto T = 1.0;// длина отрезка интегрирования

template<typename T1, typename T2>
constexpr auto max(T1 a, T2 b) { return ((a) > (b) ? (a) : (b)); }//шаблон вычсиления максимума двух чисел на этапе компиляции
template<typename T1, typename T2>
constexpr auto min(T1 a, T2 b) { return ((a) < (b) ? (a) : (b)); }//шаблон вычсиления минимума двух чисел на этапе компиляции

//правая часть дифура
template<typename T>
auto constexpr fcn(T t, T z[N], T f[N])
{

    f[0] = z[1];
    f[1] = -12.168 * (z[1] * t);

}
template<typename T>
auto constexpr dmax(T ay, T ay1, T ay2, T ay3)
{
    double w;
    w = ay;
    ay1 > w ? w = ay1 : w = ay;
    ay2 > w ? w = ay2 : w = ay;
    ay3 > w ? w = ay3 : w = ay;
   
    return w;
}

//константы в методе Дормана-Принса, числа взяты из книги Хайрер, Нерсетт, Ваннер "Решение ОДУ"

constexpr double  c2 = 1. / 5.,
c3 = 3. / 10.,
c4 = 4. / 5.,
c5 = 8. / 9.,
c6 = 1.,
c7 = 1.,
a21 = 1. / 5.,
a31 = 3. / 40.,
a32 = 9. / 40.,
a41 = 44. / 45.,
a42 = -56. / 15.,
a43 = 32. / 9.,
a51 = 19372. / 6561.,
a52 = -25360. / 2187.,
a53 = 64448. / 6561.,
a54 = -212. / 729.,
a61 = 9017. / 3168.,
a62 = -355. / 33.,
a63 = 46732. / 5247.,
a64 = 49. / 176.,
a65 = -5103. / 18656.,
a71 = 35. / 384.,
a72 = 0,
a73 = 500. / 1113.,
a74 = 125. / 192.,
a75 = -2187. / 6784.,
a76 = 11. / 84.,
b1 = 35. / 384.,
b2 = 0,
b3 = 500. / 1113.,
b4 = 125. / 192.,
b5 = -2187. / 6784.,
b6 = 11. / 84.,
b7 = 0,
r1 = 5179. / 57600.,
r2 = 0,
r3 = 7571. / 16695.,
r4 = 393. / 640.,
r5 = -92097. / 339200.,
r6 = 187. / 2100.,
r7 = 1. / 40.;

//Решение задачи Коши методом Рунге-Кутта 4 порядка, основанным на расчётных формулах Дормана-Принса
template<typename T>
auto constexpr dopri5(T* z, T tend, T eps)
{
    //Вспомогательная переменная, число вызовов fcn, общее число рассмотренных шагов, число принятых шагов, число смен шага:
    int i, reject = 0, nacc = 0, nrej = 0;

    //Вспомогательные переменные для проведения промежуточных вычислений в методе ДП и автоматического выбора шага.
    double k1[N], k2[N], k3[N], k4[N], k5[N], k6[N], k7[N], z1[N], b[N], r[N];
    double err, uround = 2.e-16, denom, fac, tph, lambda = 0.5, hnew, dglob = 0.0;
    double h = min(max(1.e-10, fabs(eps)), tend), hmax = 1, t = 0, D;
    int nsteps = 0;
    while  (eps < (tend - t) && eps * fabs(tend) < (tend - t)) {
        if  ((t + h - tend) > 0.e0) h = tend - t;
        fcn(t, z, k1);
        for (i = 0; i < (N); i++) z1[i] = z[i] + h * a21 * k1[i];
        fcn(t + h * c2, z1, k2);
        for (i = 0; i < (N); i++) z1[i] = z[i] + h * (a31 * k1[i] + a32 * k2[i]);
        fcn(t + h * c3, z1, k3);
        for (i = 0; i < (N); i++) z1[i] = z[i] + h * (a41 * k1[i] + a42 * k2[i] + a43 * k3[i]);
        fcn(t + h * c4, z1, k4);
        for (i = 0; i < (N); i++) z1[i] = z[i] + h * (a51 * k1[i] + a52 * k2[i] + a53 * k3[i] + a54 * k4[i]);
        fcn(t + h * c5, z1, k5);
        for (i = 0; i < (N); i++) z1[i] = z[i] + h * (a61 * k1[i] + a62 * k2[i] + a63 * k3[i] + a64 * k4[i] + a65 * k5[i]);
        fcn(t + h * c6, z1, k6);
        for (i = 0; i < (N); i++) z1[i] = z[i] + h * (a71 * k1[i] + a72 * k2[i] + a73 * k3[i] + a74 * k4[i] + a75 * k5[i] + a76 * k6[i]);
        fcn(t + h * c7, z1, k7);

        tph = t + h;

        //Для вычисления локальной ошибки вычисляем значение в точке x+h двумя способами:
        for (i = 0; i < (N); i++) {
            b[i] = z[i] + h * (b1 * k1[i] + b2 * k2[i] + b3 * k3[i] + b4 * k4[i] + b5 * k5[i] + b6 * k6[i] + b7 * k7[i]);
            r[i] = z[i] + h * (r1 * k1[i] + r2 * k2[i] + r3 * k3[i] + r4 * k4[i] + r5 * k5[i] + r6 * k6[i] + r7 * k7[i]);
        }
        err = 0.0;
        //Автоматический выбор шага (по формулам стр. 177-178)
        for (i = 0; i < (N); i++) 
        {
            denom = dmax(1.e-6, fabs(b[i]), fabs(z[i]), 2.e0 * uround / eps);
            err += ((b[i] - r[i]) / denom) * ((b[i] - r[i]) / denom);
        }
        err = sqrt(err / static_cast<double> (N) );
        fac = max((1.e0 / 6.e0), min(3.e0, pow(err / eps, 0.125) / .9e0));

        hnew = h / fac;
        //Если не превысили максимально  допустимую погрешность на шаге, увеличиваем счетчик числа успешно принятых шагов на 1,
        //записываем в массив y значения фазовой и сопряжённой переменных в момент времени t+h
        if  (err <= eps)
        {
            nacc++;
            nsteps++;
            for (i = 0; i < (N); i++) { z[i] = b[i]; }
            t = tph;
            if  (fabs(hnew) > hmax) hnew = hmax;
            if  (reject) hnew = min(fabs(hnew), fabs(h));
            reject = 0;
            D = z[0] * z[0] * z[0] * z[0] + z[1] * z[1] * z[1] * z[1] + 14 * z[1] * z[1] * z[0] * z[0];
            lambda = (z[0] * z[0] + z[1] * z[1] - 2 + sqrt(D)) / 2.0;
            dglob = err + dglob * exp(lambda * h);
            h = hnew;
        }
        //Если превысили максимально допустимую погрешность на шаге, то меняем шаг и пересчитываем заново с момента времени t:
        else
        {
            nrej++;
            nsteps++;
            reject = 1;
            h = hnew;
        }
    }
    printf("%le\t", dglob);
    
    return dglob;
}

int main(void) {
    int i;
    double z[N + 1], tend = 1, eps, x1, y1, glob1;


    eps = 1.e-7;
    z[0] = 0; //x(0)=0

    z[1] = 1.0; //x'(0)=z=1

    glob1 = dopri5(z, T, eps);
    x1 = z[0];
    y1 = z[1];
    for (i = 0; i < N; i++)
    {
        printf("%.8lf \t", z[i]);
    }
    
   
    return 0;
}
